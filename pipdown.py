"""PEP 503/691 package finder and downloader.

Target: Linux (Termux) on CPython 3.12+.

Finds the best-matching distribution for a PEP 508 requirement and, by
default, downloads it.  Optionally emits JSON metadata instead.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import sys
from dataclasses import dataclass, field
from functools import cached_property
from html.parser import HTMLParser
from pathlib import Path
from typing import Iterable, Iterator
from urllib.parse import parse_qs, unquote, urljoin, urlparse

import httpx
from packaging.requirements import Requirement
from packaging.specifiers import InvalidSpecifier, SpecifierSet
from packaging.tags import (
    Tag,
    compatible_tags,
    cpython_tags,
    generic_tags,
    interpreter_name,
    interpreter_version,
)
from packaging.utils import (
    InvalidWheelFilename,
    canonicalize_name,
    parse_wheel_filename,
)
from packaging.version import InvalidVersion, Version
from packaging.version import parse as parse_version

log = logging.getLogger("pkgfetch")

__all__ = [
    "Link",
    "Package",
    "TargetPython",
    "PackageFinder",
    "download",
    "main",
]

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

DEFAULT_INDEX = "https://pypi.org/simple/"

# Order matters: longer / more specific suffixes must come first.
ARCHIVE_SUFFIXES: tuple[str, ...] = (
    ".tar.gz",
    ".tgz",
    ".tar.bz2",
    ".tbz",
    ".tar.xz",
    ".txz",
    ".tar.lz",
    ".tar.lzma",
    ".tlz",
    ".zip",
    ".whl",
    ".tar",
)

HASH_ALGORITHMS: tuple[str, ...] = (
    "sha256",
    "sha512",
    "sha384",
    "sha224",
    "sha1",
    "md5",
)

SIMPLE_ACCEPT = ", ".join(
    (
        "application/vnd.pypi.simple.v1+json",
        "application/vnd.pypi.simple.v1+html; q=0.1",
        "text/html; q=0.01",
    )
)

JSON_CONTENT_TYPES = frozenset({"application/vnd.pypi.simple.v1+json"})
HTML_CONTENT_TYPES = frozenset(
    {
        "text/html",
        "application/vnd.pypi.simple.v1+html",
    }
)

CHUNK_SIZE = 64 * 1024  # 64 KiB streaming chunk


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Link:
    """A single downloadable artifact discovered on a simple index."""

    url: str
    comes_from: str | None = None
    requires_python: str | None = None
    yanked: str | None = None
    hashes: dict[str, str] = field(default_factory=dict)

    def __post_init__(self) -> None:
        # Merge any ``#sha256=...`` fragment hashes into the mapping.
        fragment = urlparse(self.url).fragment
        if not fragment:
            return
        merged = dict(self.hashes)
        for name, values in parse_qs(fragment).items():
            if name in HASH_ALGORITHMS and values:
                merged.setdefault(name, values[0])
        if merged != self.hashes:
            object.__setattr__(self, "hashes", merged)

    @property
    def url_without_fragment(self) -> str:
        return self.url.split("#", 1)[0]

    @property
    def _parsed(self):
        return urlparse(self.url_without_fragment)

    @property
    def filename(self) -> str:
        return unquote(self._parsed.path.rsplit("/", 1)[-1])

    @property
    def is_wheel(self) -> bool:
        return self.filename.endswith(".whl")

    @property
    def is_file(self) -> bool:
        return self._parsed.scheme == "file"

    @property
    def file_path(self) -> Path:
        return Path(unquote(self._parsed.path))

    def __repr__(self) -> str:
        return f"<Link {self.url}>"


@dataclass(frozen=True)
class Package:
    """A resolved ``name`` / ``version`` / ``Link`` triple."""

    name: str
    version: str
    link: Link

    @cached_property
    def parsed_version(self) -> Version:
        return parse_version(self.version)

    def as_json(self) -> dict:
        return {
            "name": self.name,
            "version": self.version,
            "link": self.link.url,
            "requires_python": self.link.requires_python,
            "yanked": self.link.yanked,
            "hashes": self.link.hashes,
        }


# ---------------------------------------------------------------------------
# Target Python
# ---------------------------------------------------------------------------


@dataclass
class TargetPython:
    """The set of wheel tags we consider installable."""

    py_ver: tuple[int, ...] | None = None
    abis: list[str] | None = None
    impl: str | None = None
    platforms: list[str] | None = None
    _tags: list[Tag] | None = field(default=None, init=False, repr=False)

    def supported_tags(self) -> list[Tag]:
        if self._tags is None:
            self._tags = self._compute_tags()
        return self._tags

    def python_version_str(self) -> str:
        """The target version as ``'3.12'``."""
        ver = self.py_ver or sys.version_info[:2]
        return ".".join(str(v) for v in ver[:2])

    def _compute_tags(self) -> list[Tag]:
        impl = self.impl or interpreter_name()
        py_ver = self.py_ver[:2] if self.py_ver else None
        nodel = "".join(map(str, py_ver)) if py_ver else interpreter_version()
        interp = f"{impl}{nodel}"

        tags: list[Tag] = []
        if impl == "cp":
            tags.extend(cpython_tags(py_ver, self.abis, self.platforms))
        else:
            tags.extend(generic_tags(interp, self.abis, self.platforms))
        tags.extend(compatible_tags(py_ver, interp, self.platforms))
        return tags


# ---------------------------------------------------------------------------
# Index parsing
# ---------------------------------------------------------------------------


class _AnchorParser(HTMLParser):
    """Extract anchors and the base URL from an HTML simple index page."""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.base_url: str | None = None
        self.anchors: list[dict[str, str]] = []

    def handle_starttag(self, tag: str, attrs) -> None:
        if tag == "base" and self.base_url is None:
            href = dict(attrs).get("href")
            if href is not None:
                self.base_url = href
        elif tag == "a":
            self.anchors.append(dict(attrs))


def _parse_html_index(response: httpx.Response) -> Iterator[Link]:
    parser = _AnchorParser()
    parser.feed(response.text)
    base = parser.base_url or str(response.url)
    for anchor in parser.anchors:
        href = anchor.get("href")
        if not href:
            continue
        url = urljoin(base, href)
        yanked = anchor.get("data-yanked")
        yield Link(
            url=url,
            comes_from=base,
            requires_python=anchor.get("data-requires-python"),
            yanked=yanked if yanked != "" else "",
        )


def _parse_json_index(response: httpx.Response) -> Iterator[Link]:
    payload = response.json()
    base = str(response.url)
    for entry in payload.get("files", ()):
        raw_url = entry.get("url")
        if not raw_url:
            continue
        yanked = entry.get("yanked")
        yield Link(
            url=urljoin(base, raw_url),
            comes_from=base,
            requires_python=entry.get("requires-python"),
            yanked=yanked if isinstance(yanked, str) else ("yanked" if yanked else None),
            hashes=entry.get("hashes") or {},
        )


def fetch_index(client: httpx.Client, url: str) -> list[Link]:
    """Fetch and parse a simple index page (HTML or JSON)."""
    response = client.get(url, headers={"Accept": SIMPLE_ACCEPT})
    response.raise_for_status()

    content_type = response.headers.get("content-type", "").split(";", 1)[0].strip().lower()
    if content_type in JSON_CONTENT_TYPES:
        return list(_parse_json_index(response))
    if content_type in HTML_CONTENT_TYPES:
        return list(_parse_html_index(response))
    raise ValueError(f"unsupported content-type: {content_type!r}")


# ---------------------------------------------------------------------------
# Link evaluation
# ---------------------------------------------------------------------------


def _strip_archive_suffix(filename: str) -> str:
    for suffix in ARCHIVE_SUFFIXES:
        if filename.endswith(suffix):
            return filename[: -len(suffix)]
    return filename


def _check_requires_python(requires: str, target: TargetPython) -> bool:
    try:
        spec = SpecifierSet(requires)
    except InvalidSpecifier:
        return True  # be permissive on malformed specifiers
    return spec.contains(target.python_version_str(), prereleases=True)


def _wheel_rank(link: Link, priorities: dict[Tag, int]) -> int:
    """Lower is better; ``len(priorities) + 1`` means "no compatible tag"."""
    worst = len(priorities) + 1
    if not link.is_wheel:
        return worst
    try:
        *_, tags = parse_wheel_filename(link.filename)
    except (InvalidWheelFilename, InvalidVersion):
        return worst
    return min((priorities.get(t, worst) for t in tags), default=worst)


def evaluate_link(
    link: Link,
    requirement: Requirement,
    target: TargetPython,
    tag_priorities: dict[Tag, int],
    *,
    allow_prereleases: bool | None,
    no_binary: bool,
    only_binary: bool,
) -> Package | None:
    """Return a ``Package`` if the link matches the requirement, else None."""
    is_wheel = link.is_wheel
    if is_wheel and no_binary:
        return None
    if not is_wheel and only_binary:
        return None

    if is_wheel:
        try:
            name, version, _, tags = parse_wheel_filename(link.filename)
        except (InvalidWheelFilename, InvalidVersion):
            return None
        if canonicalize_name(name) != canonicalize_name(requirement.name):
            return None
        if not requirement.specifier.contains(version, prereleases=allow_prereleases):
            return None
        # Enforce wheel/tag compatibility.
        if not any(t in tag_priorities for t in tags):
            return None
    else:
        if not link.filename.endswith(ARCHIVE_SUFFIXES):
            return None
        stem = _strip_archive_suffix(link.filename)
        name_part, _, version_str = stem.rpartition("-")
        if not name_part or not version_str:
            return None
        if canonicalize_name(name_part) != canonicalize_name(requirement.name):
            return None
        try:
            version = Version(version_str)
        except InvalidVersion:
            return None
        if not requirement.specifier.contains(version, prereleases=allow_prereleases):
            return None

    if link.requires_python and not _check_requires_python(link.requires_python, target):
        return None

    return Package(name=requirement.name, version=str(version), link=link)


# ---------------------------------------------------------------------------
# Package finder
# ---------------------------------------------------------------------------


class PackageFinder:
    """Collect, filter, and rank candidate distributions."""

    def __init__(
        self,
        index_urls: Iterable[str] = (),
        find_links: Iterable[str] = (),
        target_python: TargetPython | None = None,
        client: httpx.Client | None = None,
    ) -> None:
        self.sources: list[tuple[str, str]] = []
        self.sources.extend(("index", url) for url in index_urls)
        self.sources.extend(("find_links", url) for url in find_links)
        if not self.sources:
            self.sources.append(("index", DEFAULT_INDEX))

        self.target_python = target_python or TargetPython()
        self._client = client
        self._tag_priorities: dict[Tag, int] = {tag: i for i, tag in enumerate(self.target_python.supported_tags())}

    # -- HTTP client --------------------------------------------------------

    @property
    def session(self) -> httpx.Client:
        if self._client is None:
            self._client = httpx.Client(
                follow_redirects=True,
                timeout=httpx.Timeout(30.0, connect=10.0),
            )
        return self._client

    def close(self) -> None:
        if self._client is not None:
            self._client.close()
            self._client = None

    def __enter__(self) -> "PackageFinder":
        return self

    def __exit__(self, *exc) -> None:
        self.close()

    # -- Public API ---------------------------------------------------------

    def find_matches(
        self,
        requirement: Requirement,
        *,
        allow_prereleases: bool | None = None,
        no_binary: bool = False,
        only_binary: bool = False,
    ) -> list[Package]:
        """Return all matching packages, best candidate first."""
        packages: list[Package] = []
        seen: set[str] = set()

        for kind, source in self.sources:
            try:
                links = self._collect_links(kind, source, requirement)
            except (httpx.HTTPError, ValueError, OSError) as exc:
                log.warning("skipping %s %s: %s", kind, source, exc)
                continue

            for link in links:
                pkg = evaluate_link(
                    link,
                    requirement,
                    self.target_python,
                    self._tag_priorities,
                    allow_prereleases=allow_prereleases,
                    no_binary=no_binary,
                    only_binary=only_binary,
                )
                if pkg is None or pkg.link.url in seen:
                    continue
                seen.add(pkg.link.url)
                packages.append(pkg)

        packages.sort(key=self._sort_key, reverse=True)
        return packages

    # -- Internals ----------------------------------------------------------

    def _collect_links(self, kind: str, source: str, requirement: Requirement) -> list[Link]:
        if kind == "index":
            url = urljoin(source.rstrip("/") + "/", canonicalize_name(requirement.name) + "/")
        else:
            url = source
            if not url.startswith(("http://", "https://", "file://")):
                # Treat as a local directory.
                url = Path(url).absolute().as_uri()
        return fetch_index(self.session, url)

    def _sort_key(self, pkg: Package) -> tuple:
        link = pkg.link
        yanked = link.yanked is not None
        wheel_rank = _wheel_rank(link, self._tag_priorities)
        return (-int(yanked), pkg.parsed_version, -wheel_rank)


# ---------------------------------------------------------------------------
# Downloading
# ---------------------------------------------------------------------------


def _verify_file(path: Path, expected: dict[str, str]) -> bool:
    if not expected:
        return True
    for algo, want in expected.items():
        try:
            hasher = hashlib.new(algo)
        except ValueError:
            continue
        with path.open("rb") as fp:
            for chunk in iter(lambda: fp.read(CHUNK_SIZE), b""):
                hasher.update(chunk)
        if hasher.hexdigest() != want:
            return False
    return True


def download(client: httpx.Client, link: Link, dest_dir: Path) -> Path:
    """Download ``link`` into ``dest_dir`` (idempotent) and return the path."""
    dest_dir.mkdir(parents=True, exist_ok=True)

    if link.is_file:
        src = link.file_path
        if not src.is_file():
            raise FileNotFoundError(src)
        return src

    filename = link.filename or "download.bin"
    target = dest_dir / filename

    if target.exists() and _verify_file(target, link.hashes):
        log.info("using cached %s", target)
        return target

    log.info("downloading %s", link.url)
    with client.stream("GET", link.url) as response:
        response.raise_for_status()
        with target.open("wb") as fp:
            for chunk in response.iter_bytes(CHUNK_SIZE):
                fp.write(chunk)

    if not _verify_file(target, link.hashes):
        target.unlink(missing_ok=True)
        raise ValueError(f"hash mismatch for {link.url}")

    return target


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _parse_py_version(value: str) -> tuple[int, ...]:
    parts = [p for p in value.split(".") if p.isdigit()]
    if not parts:
        raise argparse.ArgumentTypeError(f"invalid Python version: {value!r}")
    return tuple(int(p) for p in parts)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="pkgfetch",
        description="Find and download Python distributions from PEP 503/691 indices.",
    )
    parser.add_argument(
        "requirement",
        type=Requirement,
        help="PEP 508 requirement string, e.g. 'requests>=2.28'.",
    )
    parser.add_argument(
        "-i",
        "--index-url",
        action="append",
        default=[],
        metavar="URL",
        help="Simple index URL (repeatable). Defaults to PyPI.",
    )
    parser.add_argument(
        "-f",
        "--find-link",
        action="append",
        default=[],
        metavar="DIR_OR_URL",
        help="Additional find-links source (repeatable).",
    )
    parser.add_argument(
        "-d",
        "--dest",
        default=".",
        metavar="DIR",
        help="Download destination directory (default: cwd).",
    )
    parser.add_argument(
        "--py-version",
        type=_parse_py_version,
        default=None,
        metavar="X.Y",
        help="Override target Python version.",
    )
    parser.add_argument(
        "--platform",
        action="append",
        default=[],
        metavar="TAG",
        help="Override target platform tag (repeatable).",
    )
    parser.add_argument(
        "--abi",
        action="append",
        default=[],
        metavar="TAG",
        help="Override ABI tag (repeatable).",
    )
    parser.add_argument(
        "--impl",
        default=None,
        metavar="IMPL",
        help="Override Python implementation (cp, pp, ...).",
    )
    parser.add_argument("--no-binary", action="store_true", help="Exclude binary wheels.")
    parser.add_argument("--only-binary", action="store_true", help="Accept only binary wheels.")
    parser.add_argument("--pre", action="store_true", help="Allow pre-release versions.")
    parser.add_argument("-a", "--all", action="store_true", help="Return every matching version, not just the latest.")
    parser.add_argument("-j", "--json", action="store_true", help="Print JSON metadata.")
    parser.add_argument("--no-download", action="store_true", help="Only resolve and print metadata; do not download.")
    parser.add_argument("-v", "--verbose", action="store_true")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)

    logging.basicConfig(
        level=logging.DEBUG if args.verbose else logging.INFO,
        format="%(levelname)s: %(message)s",
    )

    target = TargetPython(
        py_ver=args.py_version,
        abis=args.abi or None,
        impl=args.impl,
        platforms=args.platform or None,
    )

    with PackageFinder(
        index_urls=args.index_url,
        find_links=args.find_link,
        target_python=target,
    ) as finder:
        matches = finder.find_matches(
            args.requirement,
            allow_prereleases=True if args.pre else None,
            no_binary=args.no_binary,
            only_binary=args.only_binary,
        )

        if not matches:
            print("No matching distributions found.", file=sys.stderr)
            return 1

        if not args.all:
            matches = matches[:1]

        dest = Path(args.dest)
        results: list[dict] = []

        for pkg in matches:
            info = pkg.as_json()
            if not args.no_download:
                try:
                    path = download(finder.session, pkg.link, dest)
                except (httpx.HTTPError, OSError, ValueError) as exc:
                    log.error("download failed for %s: %s", pkg.link.url, exc)
                    return 2
                info["local_path"] = str(path)
            results.append(info)

    if args.json or args.no_download:
        payload = results[0] if len(results) == 1 else results
        print(json.dumps(payload, indent=2))
    else:
        for info in results:
            print(info.get("local_path", info["link"]))

    return 0


if __name__ == "__main__":
    sys.exit(main())
