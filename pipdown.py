#!/usr/bin/env python3

from __future__ import annotations

import abc
import argparse
import atexit
import contextlib
import dataclasses as dc
import email.utils
import functools
import getpass
import hashlib
import io
import inspect
import ipaddress
import itertools
import json
import logging
import mimetypes
import os
import pathlib
import posixpath
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import warnings
import zipfile
from datetime import datetime
from functools import cached_property, lru_cache
from html.parser import HTMLParser
from pathlib import Path
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Collection,
    ContextManager,
    Generator,
    Iterable,
    Iterator,
    Literal,
    Mapping,
    NamedTuple,
    Optional,
    Protocol,
    Sequence,
    Tuple,
    TypeVar,
    cast,
)
from urllib import parse as urlparse_module
from urllib.parse import ParseResult, unquote, urlparse, urlsplit
from urllib.request import url2pathname

import httpx
import packaging.requirements
from httpx._config import DEFAULT_LIMITS
from httpx._content import IteratorByteStream
from packaging.requirements import Requirement
from packaging.specifiers import InvalidSpecifier, SpecifierSet
from packaging.tags import (
    Tag,
    compatible_tags,
    cpython_tags,
    generic_tags,
    interpreter_name,
    interpreter_version,
    mac_platforms,
)
from packaging.utils import (
    BuildTag,
    InvalidWheelFilename,
    NormalizedName,
    canonicalize_name,
    parse_wheel_filename,
)
from packaging.version import InvalidVersion, Version
from packaging.version import parse as parse_version

try:
    from netrc import NetrcParseError, netrc
except ImportError:
    netrc = None  # type: ignore[assignment]
    NetrcParseError = None  # type: ignore[assignment]

try:
    import keyring
except ImportError:
    keyring = None  # type: ignore[assignment]

try:
    from requests import Session as RequestsSession, adapters
    from requests.models import PreparedRequest, Response as RequestsResponse
    from requests.auth import HTTPBasicAuth as RequestsHTTPBasicAuth
    from requests import HTTPError as RequestsHTTPError

    REQUESTS_AVAILABLE = True
except ModuleNotFoundError:
    REQUESTS_AVAILABLE = False

WINDOWS = sys.platform == "win32"
KEYRING_DISABLED = False
_netrc_warned = False
WHEEL_EXTENSION = ".whl"
BZ2_EXTENSIONS = (".tar.bz2", ".tbz")
XZ_EXTENSIONS = (".tar.xz", ".txz", ".tlz", ".tar.lz", ".tar.lzma")
ZIP_EXTENSIONS = (".zip", WHEEL_EXTENSION)
TAR_EXTENSIONS = (".tar.gz", ".tgz", ".tar")
ARCHIVE_EXTENSIONS = ZIP_EXTENSIONS + BZ2_EXTENSIONS + TAR_EXTENSIONS + XZ_EXTENSIONS
VCS_SCHEMA = ("git", "hg", "svn", "bzr")
SUPPORTED_HASHES = ("sha1", "sha224", "sha384", "sha256", "sha512", "md5")
SUPPORTED_CONTENT_TYPES = (
    "text/html",
    "application/vnd.pypi.simple.v1+html",
    "application/vnd.pypi.simple.v1+json",
)
READ_CHUNK_SIZE = 8192
DEFAULT_MAX_RETRIES = 5
DEFAULT_SECURE_ORIGINS = [
    ("https", "*", "*"),
    ("wss", "*", "*"),
    ("*", "localhost", "*"),
    ("*", "127.0.0.0/8", "*"),
    ("*", "::1/128", "*"),
    ("file", "*", "*"),
]

HTTPErrors: tuple[type[Exception], ...] = (httpx.HTTPError,)
if REQUESTS_AVAILABLE:
    HTTPErrors += (RequestsHTTPError,)  # type: ignore[misc]

logger = logging.getLogger(__name__)


T = TypeVar("T")
_V = TypeVar("_V", bound="type[VersionControl]")
AuthInfo = tuple[str, str]
MaybeAuth = Optional[tuple[str, Optional[str]]]

if TYPE_CHECKING:
    import ssl
    from typing import TypedDict
    from httpx._types import CertTypes, TimeoutTypes

    VerifyTypes = ssl.SSLContext | bool | str

    class Source(TypedDict):
        url: str
        type: str

    class DownloadReporter(Protocol):
        def __call__(self, link: "Link", completed: int, total: int | None) -> None: ...

    class UnpackReporter(Protocol):
        def __call__(self, filename: Path, completed: int, total: int | None) -> None: ...
else:
    Source = dict


def parse_query(query: str) -> dict[str, str]:
    return {k: v[0] for k, v in urlparse_module.parse_qs(query).items()}


def add_ssh_scheme_to_git_uri(uri: str) -> str:
    if "://" not in uri:
        uri = "ssh://" + uri
        parsed = urlparse(uri)
        if ":" in parsed.netloc:
            netloc, _, path_start = parsed.netloc.rpartition(":")
            path = f"/{path_start}{parsed.path}"
            uri = urlparse_module.urlunparse(parsed._replace(netloc=netloc, path=path))
    return uri


def strip_extras(name: str) -> str:
    return name.split("[", 1)[0]


def build_url_from_netloc(netloc: str, scheme: str = "https") -> str:
    if netloc.count(":") >= 2 and "@" not in netloc and ("[" not in netloc):
        netloc = f"[{netloc}]"
    return f"{scheme}://{netloc}"


def parse_netloc(netloc: str) -> tuple[str, int | None]:
    url = build_url_from_netloc(netloc)
    parsed = urlparse(url)
    return (parsed.hostname or "", parsed.port)


def url_to_path(url: str) -> Path:
    assert url.startswith("file:"), f"You can only turn file: urls into filenames (not {url!r})"
    _, netloc, path, _, _ = urlsplit(url)
    if not netloc or netloc == "localhost":
        netloc = ""
    elif WINDOWS:
        netloc = "\\\\" + netloc
    else:
        raise ValueError(f"non-local file URIs are not supported on this platform: {url!r}")
    path = url2pathname(netloc + path)
    if (
        WINDOWS
        and (not netloc)
        and (len(path) >= 3)
        and (path[0] == "/")
        and path[1].isalpha()
        and (path[2:4] in (":", ":/"))
    ):
        path = path[1:]
    return Path(path)


def is_archive_file(name: str) -> bool:
    ext = splitext(name)[1].lower()
    return ext in ARCHIVE_EXTENSIONS


def split_auth_from_netloc(netloc: str) -> tuple[tuple[str, str | None] | None, str]:
    auth, has_auth, host = netloc.rpartition("@")
    if not has_auth:
        return (None, host)
    user, has_pass, password = auth.partition(":")
    return ((unquote(user), unquote(password) if has_pass else None), host)


@lru_cache(maxsize=128)
def split_auth_from_url(url: str) -> tuple[tuple[str, str | None] | None, str]:
    parsed = urlparse(url)
    auth, netloc = split_auth_from_netloc(parsed.netloc)
    if auth is None:
        return (None, url)
    return (auth, urlparse_module.urlunparse(parsed._replace(netloc=netloc)))


@lru_cache(maxsize=128)
def compare_urls(left: str, right: str) -> bool:
    return unquote(left).rstrip("/") == unquote(right).rstrip("/")


def display_path(path: Path) -> str:
    if not path.is_absolute():
        return str(path)
    try:
        relative = path.absolute().relative_to(Path.cwd())
    except ValueError:
        return str(path)
    else:
        return str(relative)


def splitext(path: str) -> tuple[str, str]:
    base, ext = os.path.splitext(path)
    if base.lower().endswith(".tar"):
        ext = base[-4:] + ext
        base = base[:-4]
    return (base, ext)


def format_size(size: str) -> str:
    try:
        int_size = int(size)
    except (TypeError, ValueError):
        return "size unknown"
    if int_size > 1000 * 1000:
        return f"{int_size / 1000.0 / 1000:.1f} MB"
    elif int_size > 10 * 1000:
        return f"{int(int_size / 1000)} kB"
    elif int_size > 1000:
        return f"{int_size / 1000.0:.1f} kB"
    else:
        return f"{int(int_size)} bytes"


def iter_with_callback(
    iterable: Iterable[T],
    callback: Callable[[int], None],
    stepper: Callable[[T], int] = lambda _: 1,
) -> Iterator[T]:
    completed = 0
    for item in iterable:
        try:
            yield item
        finally:
            completed += stepper(item)
            callback(completed)


def commonprefix(*m: str) -> str:
    if not m:
        return ""
    m = tuple(map(os.fspath, m))
    s1 = min(m)
    s2 = max(m)
    for i, c in enumerate(s1):
        if c != s2[i]:
            return s1[:i]
    return s1


def get_netrc_auth(url: str) -> tuple[str, str] | None:
    global _netrc_warned
    if netrc is None:
        return None
    hostname = httpx.URL(url).host
    try:
        authenticator = netrc(os.getenv("NETRC"))
    except FileNotFoundError:
        return None
    except (NetrcParseError, OSError) as e:  # type: ignore[misc]
        if not _netrc_warned:
            logger.warning("Couldn't parse netrc because of %s: %s", type(e).__name__, e)
            _netrc_warned = True
        return None
    info = authenticator.authenticators(hostname)
    if info is None:
        return None
    return (info[0], info[2])


def _expect_argument(func: Callable[..., Any], argname: str) -> bool:
    sig = inspect.signature(func)
    return argname in sig.parameters


_legacy_specifier_re = re.compile(r"(==|!=|<=|>=|<|>)(\s*)([^,;\s)]*)")


@lru_cache
def fix_legacy_specifier(specifier: str) -> str:
    def fix_wildcard(match: re.Match[str]) -> str:
        operator, _, version = match.groups()
        if operator in ("==", "!="):
            return match.group(0)
        if ".*" in version:
            warnings.warn(
                ".* suffix can only be used with `==` or `!=` operators",
                FutureWarning,
                stacklevel=4,
            )
            version = version.replace(".*", ".0")
            if operator in ("<", "<="):
                operator = "<"
            elif operator in (">", ">="):
                operator = ">="
        elif "+" in version:
            warnings.warn(
                "Local version label can only be used with `==` or `!=` operators",
                FutureWarning,
                stacklevel=4,
            )
            version = version.split("+")[0]
        return f"{operator}{version}"

    return _legacy_specifier_re.sub(fix_wildcard, specifier)


class LazySequence(Sequence[T]):
    def __init__(self, data: Iterable[T]) -> None:
        self._inner = data

    def __iter__(self) -> Iterator[T]:
        self._inner, this = itertools.tee(self._inner)
        return this

    def __len__(self) -> int:
        i = 0
        for _ in self:
            i += 1
        return i

    def __bool__(self) -> bool:
        for _ in self:
            return True
        return False

    def __getitem__(self, index: int) -> T:
        if index < 0:
            raise IndexError("Negative indices are not supported")
        for i, item in enumerate(self):
            if i == index:
                return item
        raise IndexError("Index out of range")


class Response(Protocol):
    status_code: int
    headers: Mapping[str, str]
    encoding: str | None
    url: str | None

    @property
    def content(self) -> bytes: ...

    def json(self) -> dict: ...

    def iter_bytes(self, chunk_size: int | None = None) -> Iterator[bytes]: ...

    @property
    def reason_phrase(self) -> str: ...

    def raise_for_status(self) -> None: ...


class Fetcher(Protocol):
    def get(self, url: str, *, headers: Mapping[str, str] | None = None) -> Response: ...

    def head(self, url: str, *, headers: Mapping[str, str] | None = None) -> Response: ...

    def get_stream(self, url: str, *, headers: Mapping[str, str] | None = None) -> ContextManager[Response]: ...

    def __hash__(self) -> int: ...

    def iter_secure_origins(self) -> Iterable[tuple[str, str, str]]: ...


class FileByteStream(IteratorByteStream):
    def close(self) -> None:
        self._stream.close()


class LocalFSTransport(httpx.BaseTransport):
    def handle_request(self, request: httpx.Request) -> httpx.Response:
        link = Link(str(request.url))
        path = link.file_path
        if request.method != "GET":
            return httpx.Response(status_code=405)
        try:
            stats = os.stat(path)
        except OSError as exc:
            return httpx.Response(status_code=404, text=f"{type(exc).__name__}: {exc}")
        else:
            modified = email.utils.formatdate(stats.st_mtime, usegmt=True)
            content_type = mimetypes.guess_type(path)[0] or "text/plain"
            headers = {
                "Content-Type": content_type,
                "Content-Length": str(stats.st_size),
                "Last-Modified": modified,
            }
            return httpx.Response(
                status_code=200,
                headers=headers,
                stream=FileByteStream(path.open("rb")),
            )


def is_absolute_url_patch(self) -> bool:
    return self._uri_reference.scheme or self._uri_reference.host


httpx.URL.is_absolute_url = property(is_absolute_url_patch)


class PyPIClient(httpx.Client):
    def __init__(
        self,
        *,
        trusted_hosts: Iterable[str] = (),
        verify: "VerifyTypes" = True,
        cert: "CertTypes | None" = None,
        http1: bool = True,
        http2: bool = False,
        limits: httpx.Limits = DEFAULT_LIMITS,
        trust_env: bool = True,
        timeout: "TimeoutTypes" = 10.0,
        **kwargs: Any,
    ) -> None:
        self._trusted_host_ports: set[tuple[str, int | None]] = set()
        insecure_transport = httpx.HTTPTransport(
            verify=False,
            cert=cert,
            http1=http1,
            http2=http2,
            limits=limits,
            trust_env=trust_env,
        )
        mounts: dict[str, httpx.BaseTransport] = {"file://": LocalFSTransport()}
        for host in trusted_hosts:
            hostname, port = parse_netloc(host)
            self._trusted_host_ports.add((hostname, port))
            mounts[f"all://{host}"] = insecure_transport
        mounts.update(kwargs.pop("mounts", {}))
        super().__init__(
            verify=verify,
            cert=cert,
            http1=http1,
            http2=http2,
            limits=limits,
            trust_env=trust_env,
            timeout=timeout,
            mounts=mounts,
            **kwargs,
        )

    def get_stream(self, url: str, *, headers: Mapping[str, str] | None = None) -> ContextManager[httpx.Response]:
        return self.stream("GET", url, headers=headers)

    def iter_secure_origins(self) -> Iterable[tuple[str, str, str]]:
        yield from DEFAULT_SECURE_ORIGINS
        for host, port in self._trusted_host_ports:
            yield ("*", host, "*" if port is None else str(port))


class URLError(ValueError):
    pass


class VCSBackendError(URLError):
    pass


class UnpackError(RuntimeError):
    pass


class HashMismatchError(UnpackError):
    def __init__(self, link: "Link", expected: dict[str, list[str]], actual: dict[str, str]) -> None:
        self.link = link
        self.expected = expected
        self.actual = actual

    def format_hash_item(self, name: str) -> str:
        expected = self.expected[name]
        actual = self.actual[name]
        expected_prefix = f"Expected({name}): "
        actual_prefix = f"  Actual({name}): "
        sep = "\n" + " " * len(expected_prefix)
        return f"{expected_prefix}{sep.join(expected)}\n{actual_prefix}{actual}"

    def __str__(self) -> str:
        return f"Hash mismatch for {self.link.redacted}:\n" + "\n".join(
            self.format_hash_item(name) for name in sorted(self.expected)
        )


@dc.dataclass
class Link:
    url: str
    comes_from: str | None = None
    yank_reason: str | None = None
    requires_python: str | None = None
    dist_info_metadata: bool | dict[str, str] | None = None
    hashes: dict[str, str] | None = None
    upload_time: datetime | None = None
    vcs: str | None = dc.field(init=False, default=None)

    def __post_init__(self) -> None:
        vcs_prefixes = tuple((f"{schema}+" for schema in VCS_SCHEMA))
        if self.url.startswith(vcs_prefixes):
            self.vcs, _, url = self.url.partition("+")
            self.normalized = f"{self.vcs}+{add_ssh_scheme_to_git_uri(url)}"
        else:
            self.normalized = self.url

    def as_json(self) -> dict[str, Any]:
        return {
            "url": self.redacted,
            "comes_from": self.comes_from,
            "yank_reason": self.yank_reason,
            "requires_python": self.requires_python,
            "metadata": self.dist_info_link.url_without_fragment if self.dist_info_link else None,
        }

    def __ident(self) -> tuple:
        return (self.normalized, self.yank_reason, self.requires_python)

    @cached_property
    def parsed(self) -> ParseResult:
        return urlparse(self.normalized)

    def __repr__(self) -> str:
        return f"<Link {self.redacted} (from {self.comes_from})>"

    def __hash__(self) -> int:
        return hash(self.__ident())

    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Link) and self.__ident() == __o.__ident()

    @classmethod
    def from_path(cls, file_path: str | pathlib.Path) -> "Link":
        url = pathlib.Path(file_path).as_uri()
        return cls(url)

    @property
    def is_file(self) -> bool:
        return self.parsed.scheme == "file"

    @property
    def file_path(self) -> pathlib.Path:
        return url_to_path(self.url_without_fragment)

    @property
    def is_vcs(self) -> bool:
        return self.vcs is not None

    @property
    def filename(self) -> str:
        path = self.parsed.path.rsplit("@", 1)[0]
        return os.path.basename(unquote(path))

    @property
    def dist_info_link(self) -> "Link | None":
        if self.dist_info_metadata:
            return type(self)(f"{self.url_without_fragment}.metadata", self.comes_from)
        return None

    @property
    def is_wheel(self) -> bool:
        return self.filename.endswith(".whl")

    @cached_property
    def url_without_fragment(self) -> str:
        return self.parsed._replace(fragment="").geturl()

    @property
    def subdirectory(self) -> str | None:
        return self._fragment_dict.get("subdirectory")

    @property
    def _fragment_dict(self) -> dict[str, str]:
        return parse_query(self.parsed.fragment)

    @property
    def redacted(self) -> str:
        _, has_auth, host = self.parsed.netloc.rpartition("@")
        if not has_auth:
            return self.url_without_fragment
        netloc = f"***{has_auth}{host}"
        return self.parsed._replace(netloc=netloc, fragment="").geturl()

    def split_auth(self) -> tuple[tuple[str, str | None] | None, str]:
        return split_auth_from_url(self.normalized)

    @property
    def hash_name(self) -> str | None:
        return next((name for name in SUPPORTED_HASHES if name in self._fragment_dict), None)

    @property
    def hash(self) -> str | None:
        if not self.hash_name:
            return None
        return self._fragment_dict.get(self.hash_name)

    @property
    def is_yanked(self) -> bool:
        return self.yank_reason is not None

    @property
    def hash_option(self) -> dict[str, list[str]] | None:
        if self.hashes:
            return {name: [value] for name, value in self.hashes.items()}
        if self.hash_name:
            return {self.hash_name: [cast(str, self.hash)]}
        return None


class HiddenText:
    def __init__(self, secret: str, redacted: str) -> None:
        self.secret = secret
        self.redacted = redacted

    def __str__(self) -> str:
        return self.redacted

    def __repr__(self) -> str:
        return f"<URL {str(self)!r}>"


class VersionControl(abc.ABC):
    name: str
    dir_name: str

    def __init__(self, verbosity: int = 0) -> None:
        self.verbosity = verbosity

    def run_command(
        self,
        cmd: Sequence[str | HiddenText],
        cwd: Path | None = None,
        extra_env: dict[str, str] | None = None,
        log_output: bool = True,
        stdout_only: bool = False,
        extra_ok_returncodes: Collection[int] = (),
    ) -> subprocess.CompletedProcess[str]:
        env = None
        if extra_env:
            env = dict(os.environ, **extra_env)
        try:
            cmd = [self.name, *cmd]
            display_cmd = subprocess.list2cmdline(map(str, cmd))
            logger.debug("Running command %s", display_cmd)
            result = subprocess.run(
                [v.secret if isinstance(v, HiddenText) else v for v in cmd],
                cwd=str(cwd) if cwd else None,
                check=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.DEVNULL if stdout_only else subprocess.STDOUT,
                env=env,
                text=True,
            )
        except subprocess.CalledProcessError as e:
            if e.returncode in extra_ok_returncodes:
                if log_output:
                    logger.debug(e.stdout.rstrip())
                return subprocess.CompletedProcess(e.args, e.returncode, e.stdout)
            raise UnpackError(e.output) from None
        except FileNotFoundError:
            logger.debug(f"Cannot find `{self.name}`, PATH={os.environ.get('PATH')}")
            msg = f"Unable to find executable `{self.name}`, make sure it's installed in PATH."
            raise FileNotFoundError(msg) from None
        else:
            if log_output:
                logger.debug(result.stdout.rstrip())
            return result

    def _is_local_repository(self, repo: str) -> bool:
        drive, _ = os.path.splitdrive(repo)
        return repo.startswith(os.path.sep) or bool(drive)

    def get_url_and_rev_options(self, link: Link) -> tuple[HiddenText, str | None, list[str | HiddenText]]:
        parsed = link.parsed
        scheme = parsed.scheme.rsplit("+", 1)[-1]
        netloc, user, password = self.get_netloc_and_auth(parsed.netloc, scheme)
        if password is not None:
            password = HiddenText(password, "***")
        replace_dict = {
            "scheme": parsed.scheme.rsplit("+", 1)[-1],
            "netloc": netloc,
            "fragment": "",
        }
        if "@" not in parsed.path:
            rev = None
        else:
            path, _, rev = parsed.path.rpartition("@")
            if not rev:
                raise URLError(
                    f"The url {link.redacted!r} has an empty revision (after @)."
                    " You should specify a revision or remove the @ from the URL."
                )
            replace_dict["path"] = path
        args = self.make_auth_args(user, cast(HiddenText, password))
        url = parsed._replace(**replace_dict).geturl()
        hidden_url = HiddenText(url, Link(url).redacted)
        return (hidden_url, rev, args)

    def fetch(self, link: Link, location: Path) -> None:
        url, rev, args = self.get_url_and_rev_options(link)
        if not location.exists():
            return self.fetch_new(location, url, rev, args)
        if not self.is_repository_dir(location) or not compare_urls(url.secret, self.get_remote_url(location)):
            if not self.is_repository_dir(location):
                logger.debug(f"{location} is not a repository directory, removing it.")
            else:
                remote_url = self.get_remote_url(location)
                logger.debug(
                    f"{location} is a repository directory, but the remote url "
                    f"{remote_url!r} does not match the url {url!r}."
                )
            shutil.rmtree(location)
            return self.fetch_new(location, url, rev, args)
        if self.is_commit_hash_equal(location, rev):
            logger.debug("Repository %s is already up-to-date", location)
            return
        self.update(location, rev, args)

    @abc.abstractmethod
    def fetch_new(
        self,
        location: Path,
        url: HiddenText,
        rev: str | None,
        args: list[str | HiddenText],
    ) -> None: ...

    @abc.abstractmethod
    def update(self, location: Path, rev: str | None, args: list[str | HiddenText]) -> None: ...

    @abc.abstractmethod
    def get_remote_url(self, location: Path) -> str: ...

    @abc.abstractmethod
    def get_revision(self, location: Path) -> str: ...

    def is_immutable_revision(self, location: Path, link: Link) -> bool:
        return False

    def get_rev_args(self, rev: str | None) -> list[str]:
        return [rev] if rev is not None else []

    def is_commit_hash_equal(self, location: Path, rev: str | None) -> bool:
        return False

    def is_repository_dir(self, location: Path) -> bool:
        return location.joinpath(self.dir_name).exists()

    def get_netloc_and_auth(self, netloc: str, scheme: str) -> tuple[str, str | None, str | None]:
        return (netloc, None, None)

    def make_auth_args(self, user: str | None, password: HiddenText | None) -> list[str | HiddenText]:
        return []


class VcsSupport:
    def __init__(self) -> None:
        self._registry: dict[str, type[VersionControl]] = {}

    def register(self, vcs: _V) -> _V:
        self._registry[vcs.name] = vcs
        return vcs

    def unregister_all(self) -> None:
        self._registry.clear()

    def get_backend(self, name: str, verbosity: int = 0) -> VersionControl:
        try:
            return self._registry[name](verbosity=verbosity)
        except KeyError:
            raise VCSBackendError(name) from None


vcs_support = VcsSupport()


@vcs_support.register
class Git(VersionControl):
    name = "git"
    dir_name = ".git"
    HASH_REGEX = re.compile(r"^[a-fA-F0-9]{40}$")

    @staticmethod
    def looks_like_hash(sha: str) -> bool:
        return bool(Git.HASH_REGEX.match(sha))

    def get_git_version(self) -> tuple[int, ...]:
        result = self.run_command(["version"], stdout_only=True, log_output=False)
        output = result.stdout.strip()
        match = re.match(r"git version (\d+)\.(\d+)(?:\.(\d+))?", output)
        if not match:
            raise UnpackError(f"Failed to get git version: {output}")
        return tuple((int(part) for part in match.groups()))

    def fetch_new(
        self,
        location: Path,
        url: HiddenText,
        rev: str | None,
        args: list[str | HiddenText],
    ) -> None:
        rev_display = f" (revision: {rev})" if rev else ""
        logger.info("Cloning %s%s to %s", url, rev_display, display_path(location))
        env = None
        if self.verbosity <= 0:
            flags: tuple[str, ...] = ("--quiet",)
            env = {"GIT_TERMINAL_PROMPT": "0"}
        elif self.verbosity == 1:
            flags = ()
        else:
            flags = ("--verbose", "--progress")
        if self.get_git_version() >= (2, 17):
            self.run_command(
                ["clone", "--filter=blob:none", *flags, url, str(location)],
                extra_env=env,
            )
        else:
            self.run_command(["clone", *flags, url, str(location)], extra_env=env)
        if rev is not None:
            if self._should_fetch(location, rev):
                self.run_command(["fetch", "-q", url, rev], cwd=location)
                revision = self._resolve_revision(location, "FETCH_HEAD")
            else:
                revision = self._resolve_revision(location, rev)
        else:
            revision = self.get_revision(location)
        logger.info("Resolved %s to commit %s", url, revision)
        self.run_command(["reset", "--hard", "-q", revision], cwd=location)
        self._update_submodules(location)

    def _update_submodules(self, location: Path) -> None:
        if not location.joinpath(".gitmodules").exists():
            return
        self.run_command(
            ["submodule", "update", "--init", "-q", "--recursive"],
            cwd=location,
        )

    def _should_fetch(self, dest: Path, rev: str) -> bool:
        if rev.startswith("refs/"):
            return True
        if not self.looks_like_hash(rev):
            return False
        if self.has_commit(dest, rev):
            return False
        return True

    def has_commit(self, location: Path, rev: str) -> bool:
        try:
            self.run_command(
                ["rev-parse", "-q", "--verify", f"sha^{rev}"],
                cwd=location,
            )
        except UnpackError:
            return False
        else:
            return True

    def update(self, location: Path, rev: str | None, args: list[str | HiddenText]) -> None:
        self.run_command(["fetch", "-q", "--tags"], cwd=location)
        if rev is not None:
            if self._should_fetch(location, rev):
                url = self.get_remote_url(location)
                self.run_command(["fetch", "-q", url, rev], cwd=location)
                resolved = self._resolve_revision(location, "FETCH_HEAD")
            else:
                resolved = self._resolve_revision(location, rev)
        else:
            try:
                resolved = self._resolve_revision(location, "origin/HEAD")
            except UnpackError:
                resolved = self._resolve_revision(location, "HEAD")
        logger.info("Updating %s to commit %s", display_path(location), resolved)
        self.run_command(["reset", "--hard", "-q", resolved], cwd=location)

    def get_remote_url(self, location: Path) -> str:
        result = self.run_command(
            ["config", "--get-regexp", r"remote\..*\.url"],
            extra_ok_returncodes=(1,),
            cwd=location,
            stdout_only=True,
            log_output=False,
        )
        remotes = result.stdout.splitlines()
        try:
            found_remote = remotes[0]
        except IndexError:
            raise UnpackError(f"Remote not found for {display_path(location)}") from None
        for remote in remotes:
            if remote.startswith("remote.origin.url "):
                found_remote = remote
                break
        url = found_remote.split(" ")[1]
        return self._git_remote_to_pip_url(url.strip())

    def _git_remote_to_pip_url(self, url: str) -> str:
        if "://" in url:
            return url
        if os.path.exists(url):
            return Path(os.path.abspath(url)).as_uri()
        else:
            return add_ssh_scheme_to_git_uri(url)

    def _resolve_revision(self, location: Path, rev: str | None) -> str:
        if rev is None:
            rev_alternatives = ["HEAD"]
        else:
            rev_alternatives = [rev, f"origin/{rev}"]
        last_error = RuntimeError()
        for check_rev in rev_alternatives:
            try:
                result = self.run_command(
                    ["rev-parse", "--quiet", "--verify", f"{check_rev}^{{commit}}"],
                    cwd=location,
                    stdout_only=True,
                    log_output=False,
                )
            except UnpackError as e:
                last_error = e
                continue
            return result.stdout.strip()
        logger.error("Unable to resolve: %s", rev)
        raise last_error

    def get_revision(self, location: Path) -> str:
        return self._resolve_revision(location, None)

    def is_commit_hash_equal(self, location: Path, rev: str | None) -> bool:
        return rev is not None and self.get_revision(location) == rev

    def is_immutable_revision(self, location: Path, link: Link) -> bool:
        _, rev, _ = self.get_url_and_rev_options(link)
        if rev is None:
            return False
        return self.is_commit_hash_equal(location, rev)


@vcs_support.register
class Mercurial(VersionControl):
    name = "hg"
    dir_name = ".hg"

    def fetch_new(
        self,
        location: Path,
        url: HiddenText,
        rev: str | None,
        args: list[str | HiddenText],
    ) -> None:
        rev_display = f" (revision: {rev})" if rev else ""
        logger.info("Cloning hg %s%s to %s", url, rev_display, display_path(location))
        if self.verbosity <= 0:
            flags: tuple[str, ...] = ("--quiet",)
        elif self.verbosity == 1:
            flags = ()
        elif self.verbosity == 2:
            flags = ("--verbose",)
        else:
            flags = ("--verbose", "--debug")
        self.run_command(["clone", "--noupdate", *flags, url, str(location)])
        self.run_command(["update", *flags, *self.get_rev_args(rev)], cwd=location)

    def update(self, location: Path, rev: str | None, args: list[str | HiddenText]) -> None:
        self.run_command(["pull", "-q"], cwd=location)
        cmd_args = ["update", "-q", *self.get_rev_args(rev)]
        self.run_command(cmd_args, cwd=location)

    def get_revision(self, location: Path) -> str:
        current_revision = self.run_command(
            ["parents", "--template={node}"],
            log_output=False,
            stdout_only=True,
            cwd=location,
        ).stdout.strip()
        return current_revision

    def get_remote_url(self, location: Path) -> str:
        url = self.run_command(
            ["showconfig", "paths.default"],
            log_output=False,
            stdout_only=True,
            cwd=location,
        ).stdout.strip()
        if self._is_local_repository(url):
            url = Path(url).as_uri()
        return url.strip()


@vcs_support.register
class Bazaar(VersionControl):
    name = "bzr"
    dir_name = ".bzr"

    def get_rev_args(self, rev: str | None) -> list[str]:
        return ["-r", rev] if rev is not None else []

    def fetch_new(
        self,
        location: Path,
        url: HiddenText,
        rev: str | None,
        args: list[str | HiddenText],
    ) -> None:
        rev_display = f" (revision: {rev})" if rev else ""
        logger.info("Checking out %s%s to %s", url, rev_display, display_path(location))
        if self.verbosity <= 0:
            flag = "--quiet"
        elif self.verbosity == 1:
            flag = ""
        else:
            flag = f"-{'v' * self.verbosity}"
        cmd_args: list[str | HiddenText] = [
            "branch",
            flag,
            *self.get_rev_args(rev),
            url,
            str(location),
        ]
        self.run_command(cmd_args)

    def update(self, location: Path, rev: str | None, args: list[str | HiddenText]) -> None:
        self.run_command(["pull", "-q", *self.get_rev_args(rev)], cwd=location)

    def get_remote_url(self, location: Path) -> str:
        urls = self.run_command(
            ["info"],
            log_output=False,
            stdout_only=True,
            cwd=location,
        ).stdout
        for line in urls.splitlines():
            line = line.strip()
            for x in ("checkout of branch: ", "parent branch: "):
                if line.startswith(x):
                    repo = line.split(x)[1]
                    if self._is_local_repository(repo):
                        return Path(repo).as_uri()
                    return repo
        raise UnpackError(f"Remote not found for {display_path(location)}")

    def get_revision(self, location: Path) -> str:
        revision = self.run_command(
            ["revno"],
            log_output=False,
            stdout_only=True,
            cwd=location,
        ).stdout
        return revision.splitlines()[-1]

    def get_url_and_rev_options(self, link: Link) -> tuple[HiddenText, str | None, list[str | HiddenText]]:
        hidden_url, rev, args = super().get_url_and_rev_options(link)
        if hidden_url.secret.startswith("ssh://"):
            hidden_url.secret = f"bzr+{hidden_url.secret}"
            hidden_url.redacted = f"bzr+{hidden_url.redacted}"
        return (hidden_url, rev, args)


_svn_xml_url_re = re.compile(r'url="([^"]+)"')
_svn_rev_re = re.compile(r'committed-rev="(\d+)"')
_svn_info_xml_rev_re = re.compile(r'\s*revision="(\d+)"')
_svn_info_xml_url_re = re.compile(r"<url>(.*)</url>")


def is_installable_dir(path: Path) -> bool:
    for project_file in ("pyproject.toml", "setup.py"):
        if (path / project_file).exists():
            return True
    return False


@vcs_support.register
class Subversion(VersionControl):
    name = "svn"
    dir_name = ".svn"

    def get_netloc_and_auth(self, netloc: str, scheme: str) -> tuple[str, str | None, str | None]:
        if scheme == "ssh":
            return (netloc, None, None)
        user_pass, netloc = split_auth_from_netloc(netloc)
        if not user_pass:
            return (netloc, None, None)
        return (netloc, user_pass[0], user_pass[1])

    def get_rev_args(self, rev: str | None) -> list[str]:
        return ["-r", rev] if rev is not None else []

    def make_auth_args(self, user: str | None, password: HiddenText | None) -> list[str | HiddenText]:
        args: list[str | HiddenText] = []
        if user is not None:
            args.extend(["--username", user])
        if password is not None:
            args.extend(["--password", password])
        return args

    def fetch_new(
        self,
        location: Path,
        url: HiddenText,
        rev: str | None,
        args: list[str | HiddenText],
    ) -> None:
        rev_display = f" (revision: {rev})" if rev else ""
        logger.info("Checking out %s%s to %s", url, rev_display, display_path(location))
        if self.verbosity <= 0:
            flag = "--quiet"
        else:
            flag = ""
        cmd_args: list[str | HiddenText] = [
            "checkout",
            flag,
            "--non-interactive",
            *self.get_rev_args(rev),
            url,
            str(location),
        ]
        self.run_command(cmd_args)

    def update(self, location: Path, rev: str | None, args: list[str | HiddenText]) -> None:
        cmd_args: list[str] = [
            "update",
            "--non-interactive",
            *self.get_rev_args(rev),
            str(location),
        ]
        self.run_command(cmd_args)

    def get_remote_url(self, location: Path) -> str:
        orig_location = location
        while not is_installable_dir(location):
            last_location = location
            location = location.parent
            if location == last_location:
                raise UnpackError(
                    f"Could not find Python project for directory {orig_location} (tried all parent directories)"
                )
        url, _ = self._get_svn_url_rev(location)
        if url is None:
            raise UnpackError(f"Remote not found for {location}")
        return url

    def get_revision(self, location: Path) -> str:
        revision = 0
        for base, dirs, _ in os.walk(location):
            if self.dir_name not in dirs:
                dirs[:] = []
                continue
            dirs.remove(self.dir_name)
            entries_fn = os.path.join(base, self.dir_name, "entries")
            if not os.path.exists(entries_fn):
                continue
            dirurl, localrev = self._get_svn_url_rev(Path(base))
            if Path(base) == location:
                assert dirurl is not None
                base = dirurl + "/"
            elif not dirurl or not dirurl.startswith(base):
                dirs[:] = []
                continue
            revision = max(revision, localrev)
        return str(revision)

    def _get_svn_url_rev(self, location: Path) -> tuple[str | None, int]:
        entries_path = os.path.join(location, self.dir_name, "entries")
        if os.path.exists(entries_path):
            with open(entries_path) as f:
                data = f.read()
        else:
            data = ""
        url = None
        if data.startswith("8") or data.startswith("9") or data.startswith("10"):
            entries = list(map(str.splitlines, data.split("\n\x0c\n")))
            del entries[0][0]
            url = entries[0][3]
            revs = [int(d[9]) for d in entries if len(d) > 9 and d[9]] + [0]
        elif data.startswith("<?xml"):
            match = _svn_xml_url_re.search(data)
            if not match:
                raise ValueError(f"Badly formatted data: {data!r}")
            url = match.group(1)
            revs = [int(m.group(1)) for m in _svn_rev_re.finditer(data)] + [0]
        else:
            try:
                xml = self.run_command(
                    ["info", "--xml", str(location)],
                    log_output=False,
                    stdout_only=True,
                ).stdout
                match = _svn_info_xml_url_re.search(xml)
                assert match is not None
                url = match.group(1)
                revs = [int(m.group(1)) for m in _svn_info_xml_rev_re.finditer(xml)]
            except UnpackError:
                url, revs = (None, [])
        if revs:
            rev = max(revs)
        else:
            rev = 0
        return (url, rev)


_osx_arch_pat = re.compile(r"(.+)_(\d+)_(\d+)_(.+)")


def version_info_to_nodot(version_info: tuple[int, ...]) -> str:
    return "".join(map(str, version_info[:2]))


def _mac_platforms(arch: str) -> list[str]:
    match = _osx_arch_pat.match(arch)
    if match:
        name, major, minor, actual_arch = match.groups()
        mac_version = (int(major), int(minor))
        arches = ["{}_{}".format(name, arch[len("macosx_") :]) for arch in mac_platforms(mac_version, actual_arch)]
    else:
        arches = [arch]
    return arches


def _custom_manylinux_platforms(arch: str) -> list[str]:
    arches = [arch]
    arch_prefix, arch_sep, arch_suffix = arch.partition("_")
    if arch_prefix == "manylinux2014":
        if arch_suffix in {"i686", "x86_64"}:
            arches.append("manylinux2010" + arch_sep + arch_suffix)
            arches.append("manylinux1" + arch_sep + arch_suffix)
    elif arch_prefix == "manylinux2010":
        arches.append("manylinux1" + arch_sep + arch_suffix)
    return arches


def _get_custom_platforms(arch: str) -> list[str]:
    arch_prefix, *_ = arch.partition("_")
    if arch.startswith("macosx"):
        arches = _mac_platforms(arch)
    elif arch_prefix in ["manylinux2014", "manylinux2010"]:
        arches = _custom_manylinux_platforms(arch)
    else:
        arches = [arch]
    return arches


def _expand_allowed_platforms(platforms: list[str] | None) -> list[str] | None:
    if not platforms:
        return None
    seen = set()
    result = []
    for p in platforms:
        if p in seen:
            continue
        additions = [c for c in _get_custom_platforms(p) if c not in seen]
        seen.update(additions)
        result.extend(additions)
    return result


def _get_python_version(version: str) -> "packaging.tags.PythonVersion":
    if len(version) > 1:
        return (int(version[0]), int(version[1:]))
    else:
        return (int(version[0]),)


def _get_custom_interpreter(
    implementation: str | None = None,
    version: str | None = None,
) -> str:
    if implementation is None:
        implementation = interpreter_name()
    if version is None:
        version = interpreter_version()
    return f"{implementation}{version}"


def get_supported(
    version: str | None = None,
    platforms: list[str] | None = None,
    impl: str | None = None,
    abis: list[str] | None = None,
) -> list[Tag]:
    supported: list[Tag] = []
    python_version: "packaging.tags.PythonVersion | None" = None
    if version is not None:
        python_version = _get_python_version(version)
    interpreter = _get_custom_interpreter(impl, version)
    platforms = _expand_allowed_platforms(platforms)
    is_cpython = (impl or interpreter_name()) == "cp"
    if is_cpython:
        supported.extend(cpython_tags(python_version=python_version, abis=abis, platforms=platforms))
    else:
        supported.extend(generic_tags(interpreter=interpreter, abis=abis, platforms=platforms))
    supported.extend(
        compatible_tags(
            python_version=python_version,
            interpreter=interpreter,
            platforms=platforms,
        )
    )
    return supported


def is_equality_specifier(specifier: SpecifierSet) -> bool:
    return any((s.operator in ("==", "===") for s in specifier))


def parse_version_from_egg_info(egg_info: str, canonical_name: str) -> str | None:
    for i, c in enumerate(egg_info):
        if canonicalize_name(egg_info[:i]) == canonical_name and c in {"-", "_"}:
            return egg_info[i + 1 :]
    return None


class LinkMismatchError(ValueError):
    pass


@dc.dataclass
class TargetPython:
    py_ver: tuple[int, ...] | None = None
    abis: list[str] | None = None
    impl: str | None = None
    platforms: list[str] | None = None

    def __post_init__(self) -> None:
        self._valid_tags: list[Tag] | None = None

    def supported_tags(self) -> list[Tag]:
        if self._valid_tags is None:
            if self.py_ver is None:
                py_version = None
            else:
                py_version = "".join(map(str, self.py_ver[:2]))
            self._valid_tags = get_supported(py_version, self.platforms, self.impl, self.abis)
        return self._valid_tags


@dc.dataclass(frozen=True)
class Package:
    name: str
    version: str | None
    link: Link = dc.field(repr=False)

    def as_json(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "version": self.version,
            "link": self.link.as_json(),
        }


@dc.dataclass(frozen=True)
class FormatControl:
    only_binary: set[NormalizedName] = dc.field(default_factory=set)
    no_binary: set[NormalizedName] = dc.field(default_factory=set)

    def get_allowed_formats(self, canonical_name: NormalizedName) -> set[str]:
        allowed_formats = {"binary", "source"}
        if canonical_name in self.only_binary:
            allowed_formats.discard("source")
        elif canonical_name in self.no_binary:
            allowed_formats.discard("binary")
        elif ":all:" in self.only_binary:
            allowed_formats.discard("source")
        elif ":all:" in self.no_binary:
            allowed_formats.discard("binary")
        return allowed_formats

    def check_format(self, link: Link, project_name: str) -> None:
        allowed_formats = self.get_allowed_formats(canonicalize_name(project_name))
        if link.is_wheel and "binary" not in allowed_formats:
            raise LinkMismatchError(f"binary wheel is not allowed for {project_name}")
        if not link.is_wheel and "source" not in allowed_formats:
            raise LinkMismatchError(f"source distribution is not allowed for {project_name}")


@dc.dataclass
class Evaluator:
    package_name: str
    target_python: TargetPython = dc.field(default_factory=TargetPython)
    ignore_compatibility: bool = False
    allow_yanked: bool = False
    format_control: FormatControl = dc.field(default_factory=FormatControl)
    exclude_newer_than: datetime | None = None

    def __post_init__(self) -> None:
        self._canonical_name = canonicalize_name(self.package_name)

    def check_yanked(self, link: Link) -> None:
        if link.yank_reason is not None and (not self.allow_yanked):
            yank_reason = f"due to {link.yank_reason}" if link.yank_reason else ""
            raise LinkMismatchError(f"Yanked {yank_reason}")

    def check_upload_time(self, link: Link) -> None:
        if self.exclude_newer_than is not None:
            if link.upload_time is None:
                raise LinkMismatchError("Upload time is not available but exclude_newer_than is set")
            if link.upload_time > self.exclude_newer_than:
                raise LinkMismatchError(f"Upload time is newer than {self.exclude_newer_than}")

    def check_requires_python(self, link: Link) -> None:
        if not self.ignore_compatibility and link.requires_python:
            py_ver = self.target_python.py_ver or sys.version_info[:2]
            py_version = ".".join((str(v) for v in py_ver))
            try:
                requires_python = SpecifierSet(fix_legacy_specifier(link.requires_python))
            except InvalidSpecifier as e:
                raise LinkMismatchError(f"Invalid requires-python: {link.requires_python}") from e
            if not requires_python.contains(py_version, True):
                raise LinkMismatchError(
                    "The target python version({}) doesn't match the requires-python specifier {}".format(
                        py_version, link.requires_python
                    )
                )

    def validate_wheel_tag(self, tags: frozenset[Tag]) -> bool:
        if self.ignore_compatibility:
            return True
        return not tags.isdisjoint(self.target_python.supported_tags())

    def check_wheel_tags(self, filename: str) -> None:
        if self.ignore_compatibility:
            return
        tags = parse_wheel_filename(filename)[-1]
        if not self.validate_wheel_tag(tags):
            raise LinkMismatchError(f"The wheel tags in {filename} are not compatible")

    def evaluate_link(self, link: Link) -> Package | None:
        try:
            self.format_control.check_format(link, self.package_name)
            self.check_yanked(link)
            self.check_upload_time(link)
            self.check_requires_python(link)
            version: str | None = None
            if link.is_wheel:
                try:
                    wheel_info = parse_wheel_filename(link.filename)
                except (InvalidWheelFilename, InvalidVersion) as e:
                    raise LinkMismatchError(str(e)) from None
                if self._canonical_name != wheel_info[0]:
                    raise LinkMismatchError(f"The package name doesn't match {wheel_info[0]}")
                self.check_wheel_tags(link.filename)
                version = str(wheel_info[1])
            else:
                if link._fragment_dict.get("egg"):
                    egg_info = strip_extras(link._fragment_dict["egg"])
                else:
                    egg_info, ext = splitext(link.filename)
                    if not ext:
                        raise LinkMismatchError(f"Not a file: {link.filename}")
                    if ext not in ARCHIVE_EXTENSIONS:
                        raise LinkMismatchError(f"Unsupported archive format: {link.filename}")
                LOOSE_FILENAME = os.getenv("UNEARTH_LOOSE_FILENAME", "false").lower() in (
                    "1",
                    "true",
                )
                if LOOSE_FILENAME:
                    version = parse_version_from_egg_info(egg_info, self._canonical_name)
                    if version is None:
                        raise LinkMismatchError(f"Missing version in the filename: {egg_info}")
                else:
                    filename_prefix, has_version, version = egg_info.rpartition("-")
                    if not has_version:
                        raise LinkMismatchError(f"Missing version in the filename: {egg_info}")
                    if canonicalize_name(filename_prefix) != self._canonical_name:
                        raise LinkMismatchError(
                            f"The package name doesn't match {egg_info}, "
                            "set env var UNEARTH_LOOSE_FILENAME=1 to allow legacy filename."
                        )
                try:
                    Version(version)
                except InvalidVersion:
                    raise LinkMismatchError(f"Invalid version in the filename {egg_info}: {version}") from None
        except LinkMismatchError as e:
            logger.debug("Skipping link %s: %s", link, e)
            return None
        return Package(name=self.package_name, version=version, link=link)


def evaluate_package(
    package: Package,
    requirement: packaging.requirements.Requirement,
    allow_prereleases: bool | None = None,
) -> bool:
    if requirement.name:
        if canonicalize_name(package.name) != canonicalize_name(requirement.name):
            logger.debug(
                "Skipping package %s: name doesn't match %s",
                package,
                requirement.name,
            )
            return False
    if package.version and (not requirement.specifier.contains(package.version, prereleases=allow_prereleases)):
        logger.debug(
            "Skipping package %s: version doesn't match %s",
            package,
            requirement.specifier,
        )
        return False
    return True


def _get_hash(link: Link, hash_name: str, session: Fetcher) -> str:
    hasher = hashlib.new(hash_name)
    with session.get_stream(link.normalized) as resp:
        for chunk in resp.iter_bytes(chunk_size=1024 * 8):
            hasher.update(chunk)
    digest = hasher.hexdigest()
    if not link.hashes:
        link.hashes = {}
    link.hashes[hash_name] = digest
    return digest


def validate_hashes(
    package: Package,
    hashes: dict[str, list[str]],
    session: Fetcher,
) -> bool:
    if not hashes:
        return True
    link = package.link
    link_hashes = link.hash_option
    if link_hashes:
        for hash_name, allowed_hashes in hashes.items():
            if hash_name in link_hashes:
                given_hash = link_hashes[hash_name][0]
                if given_hash not in allowed_hashes:
                    return False
                return True
    hash_name, allowed_hashes = next(iter(hashes.items()))
    given_hash = _get_hash(link, hash_name, session)
    return given_hash in allowed_hashes


class LinkCollectError(Exception):
    pass


class IndexPage(NamedTuple):
    link: Link
    content: bytes
    encoding: str | None
    content_type: str


class IndexHTMLParser(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.base_url: str | None = None
        self.anchors: list[dict[str, str | None]] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag == "base" and self.base_url is None:
            base_url = dict(attrs).get("href")
            if base_url is not None:
                self.base_url = base_url
        elif tag == "a":
            self.anchors.append(dict(attrs))


def _compare_origin_part(allowed: str, actual: str) -> bool:
    return allowed == "*" or allowed == actual


def is_secure_origin(fetcher: Fetcher, location: Link) -> bool:
    _, _, scheme = location.parsed.scheme.rpartition("+")
    host, port = (location.parsed.hostname or "", location.parsed.port)
    for secure_scheme, secure_host, secure_port in fetcher.iter_secure_origins():
        if not _compare_origin_part(secure_scheme, scheme):
            continue
        try:
            addr = ipaddress.ip_address(host)
            network = ipaddress.ip_network(secure_host)
        except ValueError:
            if not _compare_origin_part(secure_host, host):
                continue
        else:
            if addr not in network:
                continue
        if not _compare_origin_part(secure_port, "*" if port is None else str(port)):
            continue
        return True
    logger.warning(
        "Skipping %s for not being trusted, please add it to `trusted_hosts` list",
        location.redacted,
    )
    return False


def parse_html_page(page: IndexPage) -> Iterable[Link]:
    parser = IndexHTMLParser()
    parser.feed(page.content.decode(page.encoding or "utf-8"))
    base_url = parser.base_url or page.link.url_without_fragment
    for anchor in parser.anchors:
        href = anchor.get("href")
        if href is None:
            continue
        url = urlparse_module.urljoin(base_url, href)
        requires_python = anchor.get("data-requires-python")
        yank_reason = anchor.get("data-yanked")
        metadata_hash = anchor.get("data-core-metadata", anchor.get("data-dist-info-metadata"))
        dist_info_metadata: bool | dict[str, str] | None = None
        if metadata_hash:
            hash_name, has_hash, hash_value = metadata_hash.partition("=")
            if has_hash:
                dist_info_metadata = {hash_name: hash_value}
            else:
                dist_info_metadata = True
        yield Link(
            url,
            base_url,
            yank_reason=yank_reason,
            requires_python=requires_python,
            dist_info_metadata=dist_info_metadata,
        )


def parse_json_response(page: IndexPage) -> Iterable[Link]:
    data = json.loads(page.content)
    base_url = page.link.url_without_fragment
    for file in data.get("files", []):
        url = file.get("url")
        if not url:
            continue
        url = urlparse_module.urljoin(base_url, url)
        requires_python: str | None = file.get("requires-python")
        yank_reason: str | None = file.get("yanked") or None
        dist_info_metadata: bool | dict[str, str] | None = file.get(
            "core-metadata", file.get("data-dist-info-metadata")
        )
        hashes: dict[str, str] | None = file.get("hashes")
        upload_time_str = file.get("upload-time")
        upload_time = None
        if upload_time_str:
            upload_time = datetime.fromisoformat(upload_time_str.replace("Z", "+00:00"))
        yield Link(
            url,
            base_url,
            yank_reason=yank_reason,
            requires_python=requires_python,
            dist_info_metadata=dist_info_metadata,
            hashes=hashes,
            upload_time=upload_time,
        )


def _is_html_file(file_url: str) -> bool:
    return mimetypes.guess_type(file_url, strict=False)[0] == "text/html"


def _get_html_response(
    session: Fetcher,
    location: Link,
    headers: Mapping[str, str] | None = None,
) -> "Response":
    if is_archive_file(location.filename):
        _ensure_index_response(session, location)
    resp = session.get(
        location.normalized,
        headers={
            "Accept": ", ".join(
                [
                    "application/vnd.pypi.simple.v1+json",
                    "application/vnd.pypi.simple.v1+html; q=0.1",
                    "text/html; q=0.01",
                ]
            ),
            **(headers or {}),
        },
    )
    _check_for_status(resp)
    _ensure_index_content_type(resp)
    return resp


def _ensure_index_response(session: Fetcher, location: Link) -> None:
    if location.parsed.scheme not in {"http", "https"}:
        raise LinkCollectError(
            "NotHTTP: the file looks like an archive but its content-type cannot be checked by a HEAD request."
        )
    resp = session.head(location.url)
    _check_for_status(resp)
    _ensure_index_content_type(resp)


def _check_for_status(resp: "Response") -> None:
    if hasattr(resp, "reason"):
        reason = resp.reason
    else:
        reason = resp.reason_phrase
    if isinstance(reason, bytes):
        try:
            reason = reason.decode("utf-8")
        except UnicodeDecodeError:
            reason = reason.decode("iso-8859-1")
    if 400 <= resp.status_code < 500:
        raise LinkCollectError(f"Client Error({resp.status_code}): {reason}")
    if 500 <= resp.status_code < 600:
        raise LinkCollectError(f"Server Error({resp.status_code}): {reason}")


def _ensure_index_content_type(resp: "Response") -> None:
    content_type = resp.headers.get("Content-Type", "Unknown")
    content_type_l = content_type.lower()
    if content_type_l.startswith(SUPPORTED_CONTENT_TYPES):
        return
    raise LinkCollectError(
        f"Content-Type unsupported: {content_type}. The only supported are {', '.join(SUPPORTED_CONTENT_TYPES)}."
    )


def fetch_page(
    session: Fetcher,
    location: Link,
    headers: Mapping[str, str] | None = None,
) -> IndexPage:
    if location.is_vcs:
        raise LinkCollectError("It is a VCS link.")
    resp = _get_html_response(session, location, headers)
    from_cache = getattr(resp, "from_cache", False)
    cache_text = " (from cache)" if from_cache else ""
    logger.debug("Fetching HTML page %s%s", location.redacted, cache_text)
    return IndexPage(
        Link(str(resp.url)),
        resp.content,
        resp.encoding,
        resp.headers["Content-Type"],
    )


def _collect_links_from_index(
    session: Fetcher,
    location: Link,
    headers: Mapping[str, str] | None = None,
) -> Iterable[Link]:
    if not is_secure_origin(session, location):
        return []
    try:
        page = fetch_page(session, location, headers)
    except LinkCollectError as e:
        logger.warning("Failed to collect links from %s: %s", location.redacted, e)
        return []
    else:
        content_type_l = page.content_type.lower()
        if content_type_l.startswith("application/vnd.pypi.simple.v1+json"):
            return parse_json_response(page)
        else:
            return parse_html_page(page)


def collect_links_from_location(
    session: Fetcher,
    location: Link,
    expand: bool = False,
    headers: Mapping[str, str] | None = None,
) -> Iterable[Link]:
    logger.debug("Collecting links from %s", location.redacted)
    if location.is_file:
        path = location.file_path
        if path.is_dir():
            if expand:
                for child in path.iterdir():
                    file_url = child.as_uri()
                    if _is_html_file(file_url):
                        yield from _collect_links_from_index(session, Link(file_url), headers)
                    else:
                        yield Link(file_url)
            else:
                index_html = Link(path.joinpath("index.html").as_uri())
                yield from _collect_links_from_index(session, index_html, headers)
        elif _is_html_file(str(path)):
            yield from _collect_links_from_index(session, location, headers)
        else:
            yield location
    else:
        if is_secure_origin(session, location) and (not location.is_vcs):
            yield location
        yield from _collect_links_from_index(session, location)


class KeyringBaseProvider(metaclass=abc.ABCMeta):
    @abc.abstractmethod
    def get_auth_info(self, url: str, username: str | None) -> AuthInfo | None: ...

    @abc.abstractmethod
    def save_auth_info(self, url: str, username: str, password: str) -> None: ...

    @abc.abstractmethod
    def delete_auth_info(self, url: str, username: str) -> None: ...


class KeyringModuleProvider(KeyringBaseProvider):
    def __init__(self) -> None:
        self.keyring = keyring

    def get_auth_info(self, url: str, username: str | None) -> AuthInfo | None:
        if hasattr(self.keyring, "get_credential"):
            logger.debug("Getting credentials from keyring for url: %s", url)
            cred = self.keyring.get_credential(url, username)
            if cred is not None:
                return (cred.username, cred.password)
        if username is None:
            username = "__token__"
        logger.debug("Getting password from keyring for: %s@%s", username, url)
        password = self.keyring.get_password(url, username)
        if password:
            return (username, password)
        return None

    def save_auth_info(self, url: str, username: str, password: str) -> None:
        self.keyring.set_password(url, username, password)

    def delete_auth_info(self, url: str, username: str) -> None:
        self.keyring.delete_password(url, username)


class KeyringCliProvider(KeyringBaseProvider):
    def __init__(self, cmd: str) -> None:
        self.keyring = cmd

    def get_auth_info(self, url: str, username: str | None) -> AuthInfo | None:
        logger.debug("Getting credentials from keyring CLI for url: %s", url)
        cred = self._get_secret(url, username or "", mode="creds")
        if cred is not None:
            username, password = cred.splitlines()
            return (username, password)
        if username is None:
            username = "__token__"
        logger.debug("Getting password from keyring CLI for %s@%s", username, url)
        password = self._get_secret(url, username)
        if password is not None:
            return (username, password)
        return None

    def save_auth_info(self, url: str, username: str, password: str) -> None:
        return self._set_password(url, username, password)

    def delete_auth_info(self, url: str, username: str) -> None:
        cmd = [self.keyring, "del", url, username]
        env = dict(os.environ, PYTHONIOENCODING="utf-8")
        subprocess.run(cmd, env=env, check=True)

    def _get_secret(
        self,
        service_name: str,
        username: str,
        mode: Literal["password", "creds"] = "password",
    ) -> str | None:
        cmd = [self.keyring, f"--mode={mode}", "get", service_name, username]
        env = dict(os.environ, PYTHONIOENCODING="utf-8")
        res = subprocess.run(cmd, stdin=subprocess.DEVNULL, capture_output=True, env=env)
        if res.returncode:
            return None
        return res.stdout.decode("utf-8").strip(os.linesep)

    def _set_password(self, service_name: str, username: str, password: str) -> None:
        if self.keyring is None:
            return None
        cmd = [self.keyring, "set", service_name, username]
        input_ = (password + os.linesep).encode("utf-8")
        env = dict(os.environ, PYTHONIOENCODING="utf-8")
        subprocess.run(cmd, input=input_, env=env, check=True)


def get_keyring_provider() -> KeyringBaseProvider | None:
    if KEYRING_DISABLED:
        return None
    try:
        return KeyringModuleProvider()
    except ImportError:
        pass
    except Exception as exc:
        logger.warning("Importing keyring failed: %s, trying to find a keyring executable.", exc)
    keyring_cmd = shutil.which("keyring")
    if keyring_cmd is not None:
        return KeyringCliProvider(keyring_cmd)
    return None


def get_keyring_auth(url: str | None, username: str | None) -> AuthInfo | None:
    if not url:
        return None
    keyring_provider = get_keyring_provider()
    if keyring_provider is None:
        return None
    try:
        return keyring_provider.get_auth_info(url, username)
    except Exception as exc:
        logger.warning("Keyring is skipped due to an exception: %s", str(exc))
        global KEYRING_DISABLED
        KEYRING_DISABLED = True
        return None


class MultiDomainBasicAuth(httpx.Auth):
    def __init__(self, prompting: bool = True, index_urls: Iterable[str] = ()) -> None:
        self.prompting = prompting
        self.index_urls = list(index_urls)
        self._cached_passwords: dict[str, AuthInfo] = {}
        self._credentials_to_save: tuple[str, str, str] | None = None

    def _get_auth_from_index_url(self, url: str) -> tuple[MaybeAuth, str | None]:
        if not url or not self.index_urls:
            return (None, None)
        target = urlsplit(url.rstrip("/") + "/")
        candidates: list[ParseResult] = []
        for index in self.index_urls:
            index = index.rstrip("/") + "/"
            auth, url_no_auth = split_auth_from_url(index)
            parsed = urlsplit(url_no_auth)
            if parsed == target:
                return (auth, index)
            if target.netloc == parsed.netloc:
                candidates.append(urlsplit(index))
        if not candidates:
            return (None, None)
        best_match = max(
            candidates,
            key=lambda x: commonprefix(x.path, target.path).rfind("/"),
        )
        index = best_match.geturl()
        return (split_auth_from_url(index)[0], index)

    def _get_new_credentials(
        self,
        original_url: str,
        *,
        allow_netrc: bool = True,
        allow_keyring: bool = False,
    ) -> tuple[str | None, str | None]:
        auth, url = split_auth_from_url(original_url)
        netloc = urlparse(url).netloc
        username, password = (None, None)
        if auth:
            username, password = auth
            if password is not None:
                logger.debug("Found credentials in url for %s", netloc)
                return cast(AuthInfo, auth)
        if _expect_argument(self._get_auth_from_index_url, "netloc"):
            index_auth, index_url = self._get_auth_from_index_url(netloc)
        else:
            index_auth, index_url = self._get_auth_from_index_url(url)
        if index_url:
            logger.debug("Found index url %s", index_url)
            if index_auth is not None:
                if index_auth[1] is not None:
                    logger.debug("Found credentials in index url for %s", netloc)
                    return cast(AuthInfo, index_auth)
                if username is None:
                    username = index_auth[0]
        if allow_netrc:
            netrc_auth = get_netrc_auth(original_url)
            if netrc_auth:
                logger.debug("Found credentials in netrc for %s", netloc)
                return cast(AuthInfo, netrc_auth)
        if allow_keyring:
            kr_auth = get_keyring_auth(index_url, username) or get_keyring_auth(netloc, username)
            if kr_auth:
                logger.debug("Found credentials in keyring for %s", netloc)
                return kr_auth
        return (username, password)

    def _get_url_and_credentials(self, original_url: str) -> tuple[str, str | None, str | None]:
        _, url = split_auth_from_url(original_url)
        netloc = urlparse(url).netloc
        username, password = self._get_new_credentials(original_url, allow_netrc=True, allow_keyring=False)
        if (username is None or password is None) and netloc in self._cached_passwords:
            un, pw = self._cached_passwords[netloc]
            if username is None or username == un:
                username, password = (un, pw)
        if username is not None or password is not None:
            self._cached_passwords[netloc] = (username or "", password or "")
        return (url, username, password)

    def __call__(self, req: "PreparedRequest") -> "PreparedRequest":
        if not REQUESTS_AVAILABLE:
            raise RuntimeError("requests is required for PreparedRequest support")
        url, username, password = self._get_url_and_credentials(cast(str, req.url))
        req.url = url
        if username is not None and password is not None:
            req = RequestsHTTPBasicAuth(username, password)(req)
        req.register_hook("response", self.handle_401)
        return req

    def auth_flow(self, request: httpx.Request) -> Generator[httpx.Request, httpx.Response, None]:
        url, username, password = self._get_url_and_credentials(str(request.url))
        request.url = httpx.URL(url)
        if username is not None and password is not None:
            basic_auth = httpx.BasicAuth(username, password)
            request = next(basic_auth.auth_flow(request))
        response = yield request
        if response.status_code != 401:
            return
        username, password = self._get_new_credentials(url, allow_netrc=False, allow_keyring=True)
        save = False
        netloc = response.url.netloc.decode()
        if password is None:
            if not self.prompting:
                return
            if _expect_argument(self._prompt_for_password, "username"):
                username, password, save = self._prompt_for_password(netloc, username)
            else:
                username, password, save = self._prompt_for_password(netloc)
        self._credentials_to_save = None
        if username is not None and password is not None:
            self._cached_passwords[netloc] = (username, password)
            if save and self._should_save_password_to_keyring():
                self._credentials_to_save = (netloc, username, password)
        basic_auth = httpx.BasicAuth(username or "", password or "")
        request = next(basic_auth.auth_flow(request))
        response = yield request
        self.warn_on_401(response)
        if self._credentials_to_save:
            self.save_credentials(response)

    def _prompt_for_password(self, netloc: str, username: str | None = None) -> tuple[str | None, str | None, bool]:
        if username is None:
            username = input(f"User for {netloc}: ")
            auth = get_keyring_auth(netloc, username)
            if auth and auth[0] is not None and (auth[1] is not None):
                return (*auth, False)
        else:
            logger.info("Username: %s", username)
        if not username:
            return (None, None, False)
        password = getpass.getpass("Password: ")
        return (username, password, True)

    def _should_save_password_to_keyring(self) -> bool:
        if get_keyring_provider() is None:
            return False
        return input("Save credentials to keyring [y/N]: ") == "y"

    def handle_401(self, resp: "RequestsResponse", **kwargs: Any) -> "RequestsResponse":
        if not REQUESTS_AVAILABLE:
            return resp
        if resp.status_code != 401:
            return resp
        parsed = urlparse(cast(str, resp.url))
        username, password = self._get_new_credentials(resp.url, allow_netrc=False, allow_keyring=True)
        save = False
        if password is None:
            if not self.prompting:
                return resp
            if _expect_argument(self._prompt_for_password, "username"):
                username, password, save = self._prompt_for_password(parsed.netloc, username)
            else:
                username, password, save = self._prompt_for_password(parsed.netloc)
        self._credentials_to_save = None
        if username is not None and password is not None:
            self._cached_passwords[parsed.netloc] = (username, password)
            if save and self._should_save_password_to_keyring():
                self._credentials_to_save = (parsed.netloc, username, password)
        resp.content
        resp.raw.release_conn()
        req = RequestsHTTPBasicAuth(username or "", password or "")(resp.request)
        req.register_hook("response", self.warn_on_401)
        if self._credentials_to_save:
            req.register_hook("response", self.save_credentials)
        new_resp = resp.connection.send(req, **kwargs)
        new_resp.history.append(resp)
        return new_resp

    def warn_on_401(self, resp: "httpx.Response | RequestsResponse", **kwargs: Any) -> None:
        if resp.status_code == 401:
            logger.warning(
                "%s Error, Credentials not correct for %s",
                resp.status_code,
                resp.request.url,
            )

    def save_credentials(self, resp: "httpx.Response | RequestsResponse", **kwargs: Any) -> None:
        keyring_provider = get_keyring_provider()
        assert keyring_provider is not None, "should never reach here without keyring"
        creds = self._credentials_to_save
        self._credentials_to_save = None
        if creds and resp.status_code < 400:
            try:
                logger.info("Saving credentials to keyring")
                keyring_provider.save_auth_info(*creds)
            except Exception:
                logger.exception("Failed to save credentials")


def noop_download_reporter(link: Link, completed: int, total: int | None) -> None:
    pass


def noop_unpack_reporter(filename: Path, completed: int, total: int | None) -> None:
    pass


def set_extracted_file_to_default_mode_plus_executable(path: str) -> None:
    os.chmod(path, 511 & ~os.umask(0) | 73)


def zip_item_is_executable(info: zipfile.ZipInfo) -> bool:
    mode = info.external_attr >> 16
    return bool(mode and stat.S_ISREG(mode) and mode & 73)


def is_within_directory(directory: str | Path, path: str | Path) -> bool:
    try:
        Path(path).relative_to(directory)
    except ValueError:
        return False
    return True


def split_leading_dir(path: str) -> list[str]:
    path = path.lstrip("/").lstrip("\\")
    if "/" in path and ("\\" in path and path.find("/") < path.find("\\") or "\\" not in path):
        return path.split("/", 1)
    elif "\\" in path:
        return path.split("\\", 1)
    else:
        return [path, ""]


def has_leading_dir(paths: Iterable[str]) -> bool:
    common_prefix = None
    for path in paths:
        prefix, _ = split_leading_dir(path)
        if not prefix:
            return False
        elif common_prefix is None:
            common_prefix = prefix
        elif prefix != common_prefix:
            return False
    return True


class HashValidator:
    def __init__(self, package_link: Link, hashes: dict[str, list[str]] | None) -> None:
        if hashes is not None:
            hashes = {k: sorted(value) for k, value in hashes.items()}
        self.allowed = hashes
        self.package_link = package_link
        self.got: dict[str, "hashlib._Hash"] = {}
        if hashes is not None:
            for name in hashes:
                try:
                    self.got[name] = hashlib.new(name)
                except (TypeError, ValueError):
                    raise UnpackError(f"Unknown hash name: {name!r}") from None

    def update(self, chunk: bytes) -> None:
        for hasher in self.got.values():
            hasher.update(chunk)

    def validate(self) -> None:
        if not self.allowed:
            return
        gots: dict[str, str] = {}
        for name, hash_list in self.allowed.items():
            got = self.got[name].hexdigest()
            if got in hash_list:
                return
            gots[name] = got
        raise HashMismatchError(self.package_link, self.allowed, gots)

    def validate_path(self, path: Path) -> None:
        with path.open("rb") as f:
            for chunk in iter(lambda: f.read(READ_CHUNK_SIZE), b""):
                self.update(chunk)
        self.validate()


def _check_downloaded(path: Path, hashes: dict[str, list[str]] | None) -> bool:
    if not path.is_file():
        return False
    try:
        HashValidator(Link.from_path(path), hashes).validate_path(path)
    except HashMismatchError:
        logger.debug("File exists at %s, but the hashes don't match", path)
        path.unlink()
        return False
    logger.debug("The file is already downloaded: %s", path)
    return True


def _unzip_archive(filename: Path, location: Path, reporter: "UnpackReporter") -> None:
    os.makedirs(location, exist_ok=True)
    zipfp = open(filename, "rb")
    with zipfile.ZipFile(zipfp, allowZip64=True) as zip:
        leading = has_leading_dir(zip.namelist())
        callback = functools.partial(reporter, filename, total=len(zip.infolist()))
        for info in iter_with_callback(zip.infolist(), callback):
            name = info.filename
            fn = name
            if leading:
                fn = split_leading_dir(name)[1]
            fn = os.path.join(location, fn)
            dir = os.path.dirname(fn)
            if not is_within_directory(location, fn):
                message = (
                    f"The zip file ({filename}) has a file ({fn}) trying to install "
                    f"outside target directory ({location})"
                )
                raise UnpackError(message)
            if fn.endswith("/") or fn.endswith("\\"):
                os.makedirs(fn, exist_ok=True)
            else:
                os.makedirs(dir, exist_ok=True)
                with zip.open(name) as fp, open(fn, "wb") as destfp:
                    shutil.copyfileobj(fp, destfp)
                if zip_item_is_executable(info):
                    set_extracted_file_to_default_mode_plus_executable(fn)


def _untar_archive(filename: Path, location: Path, reporter: "UnpackReporter") -> None:
    os.makedirs(location, exist_ok=True)
    lower_fn = str(filename).lower()
    if lower_fn.endswith(".gz") or lower_fn.endswith(".tgz"):
        mode = "r:gz"
    elif lower_fn.endswith(BZ2_EXTENSIONS):
        mode = "r:bz2"
    elif lower_fn.endswith(XZ_EXTENSIONS):
        mode = "r:xz"
    elif lower_fn.endswith(".tar"):
        mode = "r"
    else:
        logger.warning("Cannot determine compression type for file %s", filename)
        mode = "r:*"
    with tarfile.open(filename, mode, encoding="utf-8") as tar:
        leading = has_leading_dir([member.name for member in tar.getmembers()])
        callback = functools.partial(reporter, filename, total=len(tar.getmembers()))
        for member in iter_with_callback(tar.getmembers(), callback):
            fn = member.name
            if leading:
                fn = split_leading_dir(fn)[1]
            path = os.path.join(location, fn)
            if not is_within_directory(location, path):
                message = (
                    f"The tar file ({filename}) has a file ({path}) trying to install "
                    f"outside target directory ({location})"
                )
                raise UnpackError(message)
            if member.isdir():
                os.makedirs(path, exist_ok=True)
            elif member.issym():
                try:
                    tar._extract_member(member, path)
                except Exception as exc:
                    logger.warning(
                        "In the tar file %s the member %s is invalid: %s",
                        filename,
                        member.name,
                        exc,
                    )
                    continue
            else:
                try:
                    fp = tar.extractfile(member)
                except (KeyError, AttributeError) as exc:
                    logger.warning(
                        "In the tar file %s the member %s is invalid: %s",
                        filename,
                        member.name,
                        exc,
                    )
                    continue
                os.makedirs(os.path.dirname(path), exist_ok=True)
                assert fp is not None
                with open(path, "wb") as destfp:
                    shutil.copyfileobj(fp, destfp)
                fp.close()
                tar.utime(member, path)
                if member.mode & 73:
                    set_extracted_file_to_default_mode_plus_executable(path)


def unpack_archive(
    archive: Path,
    dest: Path,
    reporter: "UnpackReporter" = noop_unpack_reporter,
) -> None:
    content_type = mimetypes.guess_type(str(archive))[0]
    if content_type == "application/zip" or zipfile.is_zipfile(archive) or archive.suffix.lower() in ZIP_EXTENSIONS:
        _unzip_archive(archive, dest, reporter=reporter)
    elif (
        content_type == "application/x-gzip"
        or tarfile.is_tarfile(archive)
        or archive.suffix.lower() in TAR_EXTENSIONS + XZ_EXTENSIONS + BZ2_EXTENSIONS
    ):
        _untar_archive(archive, dest, reporter=reporter)
    else:
        raise UnpackError(f"Unknown archive type: {archive.name}")


def unpack_link(
    session: Fetcher,
    link: Link,
    download_dir: Path,
    location: Path,
    hashes: dict[str, list[str]] | None = None,
    verbosity: int = 0,
    download_reporter: "DownloadReporter" = noop_download_reporter,
    unpack_reporter: "UnpackReporter" = noop_unpack_reporter,
) -> Path:
    location.parent.mkdir(parents=True, exist_ok=True)
    if link.is_vcs:
        backend = vcs_support.get_backend(cast(str, link.vcs), verbosity=verbosity)
        download_reporter(link, 0, 1)
        backend.fetch(link, location)
        download_reporter(link, 1, 1)
        return location
    validator = HashValidator(link, hashes)
    if link.is_file:
        if link.file_path.is_dir():
            logger.info(
                "The file %s is a local directory, use it directly",
                display_path(link.file_path),
            )
            return link.file_path
        artifact = link.file_path
        validator.validate_path(artifact)
    else:
        artifact = download_dir / link.filename
        if not _check_downloaded(artifact, hashes):
            with session.get_stream(link.normalized) as resp:
                try:
                    resp.raise_for_status()
                except HTTPErrors as e:
                    raise UnpackError(f"Download failed: {e}") from None
                try:
                    total = int(resp.headers["Content-Length"])
                except (KeyError, ValueError, TypeError):
                    total = None
                if getattr(resp, "from_cache", False):
                    logger.info("Using cached %s", link)
                else:
                    size = format_size(resp.headers.get("Content-Length", ""))
                    logger.info("Downloading %s (%s)", link, size)
                with artifact.open("wb") as f:
                    callback = functools.partial(download_reporter, link, total=total)
                    for chunk in iter_with_callback(
                        resp.iter_bytes(chunk_size=READ_CHUNK_SIZE),
                        callback,
                        stepper=len,
                    ):
                        if chunk:
                            validator.update(chunk)
                            f.write(chunk)
            validator.validate()
    if link.is_wheel:
        if link.is_file:
            return artifact
        target_file = location / link.filename
        if target_file != artifact:
            os.replace(artifact, target_file)
        return target_file
    unpack_archive(artifact, location, reporter=unpack_reporter)
    return location


class BestMatch(NamedTuple):
    best: Package | None
    applicable: Sequence[Package]
    candidates: Sequence[Package]


def _check_legacy_session(session: Any) -> None:
    if not REQUESTS_AVAILABLE:
        return
    if isinstance(session, RequestsSession):
        warnings.warn(
            "The legacy requests.Session is used, which is deprecated and will be "
            "removed in the next release. Please use `httpx.Client` instead.",
            DeprecationWarning,
            stacklevel=2,
        )


class PackageFinder:
    def __init__(
        self,
        session: Fetcher | None = None,
        *,
        index_urls: Iterable[str] = (),
        find_links: Iterable[str] = (),
        trusted_hosts: Iterable[str] = (),
        target_python: TargetPython | None = None,
        ignore_compatibility: bool = False,
        no_binary: Iterable[str] = (),
        only_binary: Iterable[str] = (),
        prefer_binary: Iterable[str] = (),
        respect_source_order: bool = False,
        verbosity: int = 0,
        exclude_newer_than: datetime | None = None,
    ) -> None:
        self.sources: list[Source] = []
        for url in index_urls:
            self.add_index_url(url)
        for url in find_links:
            self.add_find_links(url)
        if not self.sources:
            self.add_index_url("https://pypi.org/simple/")
        self.target_python = target_python or TargetPython()
        self.ignore_compatibility = ignore_compatibility
        self.no_binary = {canonicalize_name(name) for name in no_binary}
        self.only_binary = {canonicalize_name(name) for name in only_binary}
        self.prefer_binary = {canonicalize_name(name) for name in prefer_binary}
        self.trusted_hosts = trusted_hosts
        _check_legacy_session(session)
        self._session = session
        self.respect_source_order = respect_source_order
        self.verbosity = verbosity
        self.exclude_newer_than = exclude_newer_than
        self.headers: dict[str, str] = {}
        self._tag_priorities = {tag: i for i, tag in enumerate(self.target_python.supported_tags())}

    @property
    def session(self) -> Fetcher:
        if self._session is None:
            index_urls = [source["url"] for source in self.sources if source["type"] == "index"]
            session = PyPIClient(trusted_hosts=self.trusted_hosts)
            session.auth = MultiDomainBasicAuth(index_urls=index_urls)
            atexit.register(session.close)
            self._session = session
        return self._session

    def add_index_url(self, url: str) -> None:
        self.sources.append({"url": url, "type": "index"})

    def add_find_links(self, url: str) -> None:
        self.sources.append({"url": url, "type": "find_links"})

    def build_evaluator(self, package_name: str, allow_yanked: bool = False) -> Evaluator:
        format_control = FormatControl(no_binary=self.no_binary, only_binary=self.only_binary)
        return Evaluator(
            package_name=package_name,
            target_python=self.target_python,
            ignore_compatibility=self.ignore_compatibility,
            allow_yanked=allow_yanked,
            format_control=format_control,
            exclude_newer_than=self.exclude_newer_than,
        )

    def _build_index_page_link(self, index_url: str, package_name: str) -> Link:
        url = posixpath.join(index_url, canonicalize_name(package_name)) + "/"
        return self._build_find_link(url)

    def _build_find_link(self, find_link: str) -> Link:
        if os.path.exists(find_link):
            return Link.from_path(os.path.abspath(find_link))
        elif "://" in find_link:
            return Link(find_link)
        raise ValueError(f"Invalid find link or non-existing path: {find_link}")

    def _evaluate_links(self, links: Iterable[Link], evaluator: Evaluator) -> Iterable[Package]:
        return filter(None, map(evaluator.evaluate_link, links))

    def _evaluate_packages(
        self,
        packages: Iterable[Package],
        requirement: packaging.requirements.Requirement,
        allow_prereleases: bool | None = None,
    ) -> Iterable[Package]:
        evaluator = functools.partial(
            evaluate_package,
            requirement=requirement,
            allow_prereleases=allow_prereleases,
        )
        first_iter, second_iter = itertools.tee(packages)
        check, it = itertools.tee(filter(evaluator, first_iter))
        if next(check, None) is None and allow_prereleases is None:
            evaluator = functools.partial(evaluate_package, requirement=requirement, allow_prereleases=True)
            it = filter(evaluator, second_iter)
        return it

    def _evaluate_hashes(self, packages: Iterable[Package], hashes: dict[str, list[str]]) -> Iterable[Package]:
        evaluator = functools.partial(validate_hashes, hashes=hashes, session=self.session)
        return filter(evaluator, packages)

    def _sort_key(self, package: Package) -> tuple:
        link = package.link
        pri = len(self._tag_priorities) + 1
        build_tag: BuildTag = ()
        prefer_binary = False
        if link.is_wheel:
            *_, build_tag, file_tags = parse_wheel_filename(link.filename)
            pri = min(
                (self._tag_priorities.get(tag, pri - 1) for tag in file_tags),
                default=pri - 1,
            )
            if canonicalize_name(package.name) in self.prefer_binary or ":all:" in self.prefer_binary:
                prefer_binary = True
        return (
            -int(link.is_yanked),
            int(prefer_binary),
            parse_version(package.version) if package.version is not None else 0,
            -pri,
            build_tag,
        )

    def _find_packages(self, package_name: str, allow_yanked: bool = False) -> Iterable[Package]:
        evaluator = self.build_evaluator(package_name, allow_yanked)

        def find_one_source(source: Source) -> Iterable[Package]:
            if source["type"] == "index":
                link = self._build_index_page_link(source["url"], package_name)
                result = self._evaluate_links(
                    collect_links_from_location(self.session, link, headers=self.headers),
                    evaluator,
                )
            else:
                link = self._build_find_link(source["url"])
                result = self._evaluate_links(
                    collect_links_from_location(self.session, link, expand=True, headers=self.headers),
                    evaluator,
                )
            if self.respect_source_order:
                return sorted(result, key=self._sort_key, reverse=True)
            return result

        all_packages = itertools.chain.from_iterable(map(find_one_source, self.sources))
        if self.respect_source_order:
            return all_packages
        return sorted(all_packages, key=self._sort_key, reverse=True)

    def find_all_packages(
        self,
        package_name: str,
        allow_yanked: bool = False,
        hashes: dict[str, list[str]] | None = None,
    ) -> Sequence[Package]:
        return LazySequence(self._evaluate_hashes(self._find_packages(package_name, allow_yanked), hashes=hashes or {}))

    def _find_packages_from_requirement(
        self,
        requirement: packaging.requirements.Requirement,
        allow_yanked: bool | None = None,
    ) -> Generator[Package, None, None]:
        if allow_yanked is None:
            allow_yanked = is_equality_specifier(requirement.specifier)
        if requirement.url:
            yield Package(requirement.name, None, link=Link(requirement.url))
        else:
            yield from self._find_packages(requirement.name, allow_yanked)

    def find_matches(
        self,
        requirement: packaging.requirements.Requirement | str,
        allow_yanked: bool | None = None,
        allow_prereleases: bool | None = None,
        hashes: dict[str, list[str]] | None = None,
    ) -> Sequence[Package]:
        if isinstance(requirement, str):
            requirement = packaging.requirements.Requirement(requirement)
        return LazySequence(
            self._evaluate_hashes(
                self._evaluate_packages(
                    self._find_packages_from_requirement(requirement, allow_yanked),
                    requirement,
                    allow_prereleases,
                ),
                hashes=hashes or {},
            )
        )

    def find_best_match(
        self,
        requirement: packaging.requirements.Requirement | str,
        allow_yanked: bool | None = None,
        allow_prereleases: bool | None = None,
        hashes: dict[str, list[str]] | None = None,
    ) -> BestMatch:
        if isinstance(requirement, str):
            requirement = packaging.requirements.Requirement(requirement)
        packages = self._find_packages_from_requirement(requirement, allow_yanked)
        first_iter, second_iter = itertools.tee(packages)
        candidates = LazySequence(first_iter)
        applicable_candidates = LazySequence(
            self._evaluate_hashes(
                self._evaluate_packages(second_iter, requirement, allow_prereleases),
                hashes=hashes or {},
            )
        )
        best_match = next(iter(applicable_candidates), None)
        return BestMatch(best_match, applicable_candidates, candidates)

    def download_and_unpack(
        self,
        link: Link,
        location: str | pathlib.Path,
        download_dir: str | pathlib.Path | None = None,
        hashes: dict[str, list[str]] | None = None,
        download_reporter: "DownloadReporter" = noop_download_reporter,
        unpack_reporter: "UnpackReporter" = noop_unpack_reporter,
    ) -> pathlib.Path:
        if hashes is None:
            hashes = link.hash_option
        with contextlib.ExitStack() as stack:
            if download_dir is None:
                download_dir = stack.enter_context(TemporaryDirectory(prefix="unearth-download-"))
            file = unpack_link(
                self.session,
                link,
                pathlib.Path(download_dir),
                pathlib.Path(location),
                hashes,
                verbosity=self.verbosity,
                download_reporter=download_reporter,
                unpack_reporter=unpack_reporter,
            )
        return file.joinpath(link.subdirectory) if link.subdirectory else file


@dc.dataclass(frozen=True)
class CLIArgs:
    requirement: Requirement
    verbose: bool
    index_urls: list[str]
    find_links: list[str]
    trusted_hosts: list[str]
    no_binary: bool
    only_binary: bool
    prefer_binary: bool
    all: bool
    link_only: bool
    download: str | None
    py_ver: tuple[int, ...] | None
    abis: list[str] | None
    impl: str | None
    platforms: list[str] | None


def _setup_logger(verbosity: bool) -> None:
    logger = logging.getLogger("unearth")
    logger.setLevel(logging.DEBUG if verbosity else logging.WARNING)
    handler = logging.StreamHandler()
    handler.setLevel(logging.DEBUG)
    formatter = logging.Formatter("%(levelname)s: %(message)s")
    handler.setFormatter(formatter)
    logger.addHandler(handler)


def comma_split(arg: str) -> list[str]:
    return arg.split(",")


def to_py_ver(arg: str) -> tuple[int, ...]:
    return tuple(int(i) for i in arg.split(".") if i.isdigit())


def cli_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Find and download packages from a PEP 508 requirement string.",
    )
    parser.add_argument(
        "requirement",
        type=Requirement,
        help="A PEP 508 requirement string, e.g. 'requests>=2.18.4'.",
    )
    parser.add_argument("--verbose", "-v", action="store_true", help="Enable verbose logging.")
    parser.add_argument(
        "--index-url",
        "-i",
        metavar="URL",
        dest="index_urls",
        action="append",
        help="(Multiple)(PEP 503)Simple Index URLs.",
    )
    parser.add_argument(
        "--find-link",
        "-f",
        dest="find_links",
        metavar="LOCATION",
        action="append",
        help="(Multiple)URLs or locations to find links from.",
    )
    parser.add_argument(
        "--trusted-host",
        dest="trusted_hosts",
        metavar="HOST",
        action="append",
        help="(Multiple)Trusted hosts that should skip the verification.",
    )
    parser.add_argument(
        "--no-binary",
        action="store_true",
        help="Exclude binary packages from the results.",
    )
    parser.add_argument(
        "--only-binary",
        action="store_true",
        help="Only include binary packages in the results.",
    )
    parser.add_argument(
        "--prefer-binary",
        action="store_true",
        help="Prefer binary packages even if sdist candidates of newer versions exist.",
    )
    parser.add_argument("--all", action="store_true", help="Return all applicable versions.")
    parser.add_argument(
        "--link-only",
        "-L",
        action="store_true",
        help="Only return links instead of a JSON object.",
    )
    parser.add_argument(
        "--download",
        "-d",
        nargs="?",
        const=".",
        metavar="DIR",
        help="Download the package(s) to DIR.",
    )
    group = parser.add_argument_group("Target Python options")
    group.add_argument(
        "--python-version",
        "--py",
        dest="py_ver",
        type=to_py_ver,
        help="Target Python version. e.g. 3.11.0",
    )
    group.add_argument(
        "--abis",
        type=comma_split,
        help="Comma-separated list of ABIs. e.g. cp39,cp310",
    )
    group.add_argument(
        "--implementation",
        "--impl",
        dest="impl",
        help="Python implementation. e.g. cp,pp,jy,ip",
    )
    group.add_argument(
        "--platforms",
        type=comma_split,
        help="Comma-separated list of platforms. e.g. win_amd64,linux_x86_64",
    )
    return parser


def get_dest_for_package(dest: str, link: Link) -> str:
    if link.is_wheel:
        return dest
    filename = link.filename.rsplit("@", 1)[0]
    fn, _ = splitext(filename)
    return os.path.join(dest, fn)


def main(argv: list[str] | None = None) -> None:
    parser = cli_parser()
    args = CLIArgs(**vars(parser.parse_args(argv)))
    _setup_logger(args.verbose)
    name = args.requirement.name
    target_python = TargetPython(args.py_ver, args.abis, args.impl, args.platforms)
    finder = PackageFinder(
        index_urls=args.index_urls or [],
        find_links=args.find_links or [],
        trusted_hosts=args.trusted_hosts or [],
        target_python=target_python,
        no_binary=[name] if args.no_binary else [],
        only_binary=[name] if args.only_binary else [],
        prefer_binary=[name] if args.prefer_binary else [],
        verbosity=int(args.verbose),
    )
    matches = list(finder.find_matches(args.requirement))
    if not matches:
        print("No matches are found.", file=sys.stderr)
        sys.exit(1)
    if not args.all:
        matches = matches[:1]
    result = []
    if args.download:
        os.makedirs(args.download, exist_ok=True)
    with tempfile.TemporaryDirectory("unearth-download-") as download_dir:
        for match in matches:
            data = match.as_json()
            if args.download is not None:
                dest = get_dest_for_package(args.download, match.link)
                data["local_path"] = finder.download_and_unpack(
                    match.link,
                    dest,
                    download_dir,
                ).as_posix()
            result.append(data)
    if args.link_only:
        for item in result:
            print(item["link"]["url"])
            if "local_path" in item:
                print("  ==>", item["local_path"])
    else:
        print(json.dumps(result[0] if len(result) == 1 else result, indent=2))


__all__ = [
    "BestMatch",
    "HashMismatchError",
    "Link",
    "Package",
    "PackageFinder",
    "Source",
    "TargetPython",
    "URLError",
    "UnpackError",
    "VCSBackendError",
    "vcs_support",
]

if __name__ == "__main__":
    sys.exit(main())
