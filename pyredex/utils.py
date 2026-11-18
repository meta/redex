#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.


# pyre-strict


import argparse
import glob
import inspect
import json
import logging
import multiprocessing
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import timeit
import typing
import zipfile
from contextlib import contextmanager
from os.path import basename, dirname, isfile, join

import packaging.version
from pyredex.logger import log


IS_WINDOWS: bool = os.name == "nt"
LOGGER: logging.Logger = logging.getLogger(__name__)
temp_dirs: typing.List[str] = []


def abs_glob(directory: str, pattern: str = "*") -> typing.Generator[str, None, None]:
    """
    Returns all files that match the specified glob inside a directory.
    Returns absolute paths. Does not return files that start with '.'
    """
    for result in glob.glob(join(directory, pattern)):
        yield join(directory, result)


def make_temp_dir(name: str = "", debug: bool = False) -> str:
    """Make a temporary directory which will be automatically deleted"""
    global temp_dirs
    directory = tempfile.mkdtemp(name)
    if not debug:
        temp_dirs.append(directory)
    return directory


def remove_temp_dirs() -> None:
    global temp_dirs
    for directory in temp_dirs:
        shutil.rmtree(directory)


def with_temp_cleanup(
    fn: typing.Callable[[], None], always_clean: bool = False
) -> None:
    success = always_clean
    try:
        fn()
        success = True
    finally:
        if success:
            with timed_scope("Cleaning up temporary directories"):
                remove_temp_dirs()


class _FindAndroidBuildToolHelper:
    def __init__(self) -> None:
        self.sdk_search_order: typing.List[
            typing.Tuple[
                str,
                typing.Callable[[], typing.Optional[typing.List[str]]],
                typing.Callable[[], typing.Optional[typing.List[str]]],
            ]
        ] = [
            (
                "Env",
                _FindAndroidBuildToolHelper.find_android_path_by_env,
                _FindAndroidBuildToolHelper.find_android_build_tools_by_env,
            ),
            (
                "Buck",
                self.find_android_path_by_buck,
                self.find_android_build_tools_by_buck,
            ),
        ]
        self.root_dir_for_buck: typing.Optional[str] = None
        self.tool_overrides: typing.Dict[str, str] = {}
        self.omit_sdk_tool_discovery: bool = False

    def add_tool_override(self, tool_name: str, path: str) -> None:
        self.tool_overrides[tool_name] = path

    def find(self, tool_name: str, tool: str) -> str:
        if tool_name in self.tool_overrides:
            res = self.tool_overrides[tool_name]
            LOGGER.debug("Using tool override: %s -> %s", tool_name, res)
            return res

        if self.omit_sdk_tool_discovery:
            raise RuntimeError(
                f"Path for {tool} was not provided and the --omit-sdk-tool-discovery flag was set requiring tool paths to be explicitly provided."
            )

        result, _ = self._run(tool)
        if result:
            return result

        # Try again with more debug messages (the under the hood call to buck audit
        # seems to not always return a result)
        old_level = logging.getLogger().getEffectiveLevel()
        logging.getLogger().setLevel(logging.DEBUG)
        result, attempts = self._run(tool)
        if result:
            logging.getLogger().setLevel(old_level)
            return result

        raise RuntimeError(f'Could not find {tool}, searched {", ".join(attempts)}')

    def _run(self, tool: str) -> typing.Tuple[typing.Optional[str], typing.List[str]]:
        attempts: typing.List[str] = []

        def try_find(
            name: str,
            base_dir_fn: typing.Callable[[], typing.Optional[typing.List[str]]],
        ) -> typing.Optional[str]:
            try:
                if base_dir_fn is None:
                    return None
                base_dirs = base_dir_fn()
                if not base_dirs:
                    attempts.append(name + ":<Nothing>")
                    return None
                for base_dir in base_dirs:
                    candidate = join(base_dir, tool)
                    if os.path.exists(candidate):
                        return candidate
                    attempts.append(name + ":" + base_dir)
            except BaseException:
                pass
            return None

        for name, _, base_tools_fn in self.sdk_search_order:
            LOGGER.debug("Attempting %s to find %s", name, tool)
            candidate = try_find(name, base_tools_fn)
            if candidate:
                return candidate, attempts

        # By `PATH`.
        LOGGER.debug("Attempting PATH to find %s", tool)
        tool_path = shutil.which(tool)
        if tool_path is not None:
            return tool_path, attempts
        attempts.append("PATH")

        return None, attempts

    def set_omit_sdk_tool_discovery(self) -> None:
        self.omit_sdk_tool_discovery = True

    @staticmethod
    def _find_biggest_build_tools_version(base: str) -> typing.Optional[str]:
        VERSION_REGEXP = r"\d+\.\d+\.\d+$"
        build_tools = join(base, "build-tools")
        version = max(
            (
                "0.0.1",
                *[d for d in os.listdir(build_tools) if re.match(VERSION_REGEXP, d)],
            ),
            key=packaging.version.parse,
        )
        if version == "0.0.1":
            LOGGER.debug(
                "No version found in %s: %s", build_tools, os.listdir(build_tools)
            )
            return None
        LOGGER.debug("max build tools version: %s", version)
        return join(build_tools, version)

    @staticmethod
    def _filter_none_not_exists_ret_none(
        input: typing.Optional[typing.List[typing.Optional[str]]],
    ) -> typing.Optional[typing.List[str]]:
        if input is None:
            LOGGER.debug("Filtering an input None to None")
            return None
        filtered = [p for p in input if p and os.path.exists(p)]
        ret_val = filtered if filtered else None
        LOGGER.debug("Filtered %s to %s = %s", input, filtered, ret_val)
        return ret_val

    @staticmethod
    def find_android_path_by_env() -> typing.Optional[typing.List[str]]:
        env_values: typing.List[typing.Optional[str]] = [
            os.environ[key]
            for key in ["ANDROID_SDK", "ANDROID_HOME"]
            if key in os.environ
        ]
        LOGGER.debug("Android ENV values = %s", env_values)
        return _FindAndroidBuildToolHelper._filter_none_not_exists_ret_none(env_values)

    @staticmethod
    def find_android_build_tools_by_env() -> typing.Optional[typing.List[str]]:
        base = _FindAndroidBuildToolHelper.find_android_path_by_env()
        LOGGER.debug("Android Build Tools base by env = %s", base)
        if not base:
            return None

        return _FindAndroidBuildToolHelper._filter_none_not_exists_ret_none(
            [
                _FindAndroidBuildToolHelper._find_biggest_build_tools_version(p)
                for p in base
            ]
        )

    def add_android_sdk_path(self, path: str) -> None:
        self.sdk_search_order.insert(
            0,
            (
                f"Path:{path}",
                lambda: _FindAndroidBuildToolHelper._filter_none_not_exists_ret_none(
                    [
                        # For backwards compatibility
                        *[
                            dirname(dirname(p))
                            for p in [path]
                            if basename(dirname(p)) == "build-tools"
                        ],
                        path,
                    ]
                ),
                lambda: _FindAndroidBuildToolHelper._filter_none_not_exists_ret_none(
                    [
                        _FindAndroidBuildToolHelper._find_biggest_build_tools_version(
                            path
                        ),
                        path,  # For backwards compatibility.
                    ]
                ),
            ),
        )

    def _load_android_buckconfig_values(self) -> typing.Dict[str, typing.Any]:
        cmd = ["buck2", "audit", "config", "android", "--json"]
        rdfb = self.root_dir_for_buck
        cwd = rdfb if rdfb is not None else os.getcwd()
        # Set NO_BUCKD to minimize disruption to any currently running buckd
        env = dict(os.environ)
        env["NO_BUCKD"] = "1"
        raw = subprocess.check_output(cmd, cwd=cwd, stderr=subprocess.DEVNULL, env=env)
        return json.loads(raw)

    def find_android_path_by_buck(self) -> typing.Optional[typing.List[str]]:
        LOGGER.debug("Computing SDK path from buck")
        try:
            buckconfig = self._load_android_buckconfig_values()
        except BaseException as e:
            LOGGER.debug("Failed loading buckconfig: %s", e)
            return None
        if "android.sdk_path" not in buckconfig:
            LOGGER.debug("android.sdk_path is not in buckconfig")
            return None
        LOGGER.debug(
            "buckconfig android.sdk_path = %s", buckconfig.get("android.sdk_path")
        )
        return _FindAndroidBuildToolHelper._filter_none_not_exists_ret_none(
            [buckconfig.get("android.sdk_path")]
        )

    def find_android_build_tools_by_buck(self) -> typing.Optional[typing.List[str]]:
        LOGGER.debug("Computing SDK path from buck")
        try:
            buckconfig = self._load_android_buckconfig_values()
        except BaseException as e:
            LOGGER.debug("Failed loading buckconfig: %s", e)
            return None
        if "android.sdk_path" not in buckconfig:
            LOGGER.debug("android.sdk_path is not in buckconfig")
            return None
        sdk_path = buckconfig.get("android.sdk_path")
        LOGGER.debug("buckconfig android.sdk_path = %s", sdk_path)

        if "android.build_tools_version" in buckconfig:
            version = buckconfig["android.build_tools_version"]
            LOGGER.debug("buckconfig android.build_tools_version is %s", version)
            assert isinstance(sdk_path, str)
            return _FindAndroidBuildToolHelper._filter_none_not_exists_ret_none(
                [join(sdk_path, "build-tools", version)]
            )
        else:
            LOGGER.debug("No android.build_tools_version in buck-config")
            return _FindAndroidBuildToolHelper._filter_none_not_exists_ret_none(
                [
                    _FindAndroidBuildToolHelper._find_biggest_build_tools_version(
                        sdk_path
                    )
                ]
            )


FIND_HELPER: _FindAndroidBuildToolHelper = _FindAndroidBuildToolHelper()


def add_android_sdk_path(path: str) -> None:
    FIND_HELPER.add_android_sdk_path(path)


def set_root_dir_for_buck(path: str) -> None:
    FIND_HELPER.root_dir_for_buck = path


def add_tool_override(tool_name: str, path: str) -> None:
    FIND_HELPER.add_tool_override(tool_name, path)


def get_android_sdk_path() -> str:
    attempts = []
    for name, base_dir_fn, _ in FIND_HELPER.sdk_search_order:
        LOGGER.debug("Attempting %s to find SDK path", name)
        candidate = base_dir_fn()
        if candidate:
            return candidate[0]
        attempts.append(name)

    raise RuntimeError(f'Could not find SDK path, searched {", ".join(attempts)}')


def omit_sdk_tool_discovery() -> None:
    FIND_HELPER.set_omit_sdk_tool_discovery()


def find_apksigner() -> str:
    return FIND_HELPER.find("apksigner", "apksigner.bat" if IS_WINDOWS else "apksigner")


def find_zipalign() -> str:
    return FIND_HELPER.find("zipalign", "zipalign.exe" if IS_WINDOWS else "zipalign")


def remove_signature_files(extracted_apk_dir: str) -> None:
    for f in abs_glob(extracted_apk_dir, "META-INF/*"):
        cert_path = join(extracted_apk_dir, f)
        if isfile(cert_path):
            os.remove(cert_path)


def sign_apk(
    sign_v4: typing.Optional[bool],
    keystore: str,
    keypass: str,
    keyalias: str,
    apk: str,
    ignore_apksigner: bool = False,
) -> None:
    def run() -> None:
        subprocess.check_call(
            shlex.split(find_apksigner())
            + [
                "sign",
                "--v1-signing-enabled",
                "--v2-signing-enabled",
            ]
            + (
                []
                if sign_v4 is None
                else (["--v4-signing-enabled", "true" if sign_v4 else "false"])
            )
            + [
                "--ks",
                keystore,
                "--ks-pass",
                "pass:" + keypass,
                "--ks-key-alias",
                keyalias,
                apk,
            ],
            stdout=sys.stderr,
        )

    if ignore_apksigner:
        try:
            run()
        except FileNotFoundError:
            LOGGER.warning("Failed to find apksigner binary. Continuing...")
    else:
        run()


def remove_comments_from_line(line: str) -> str:
    (found_backslash, in_quote) = (False, False)
    for idx, c in enumerate(line):
        if c == "\\" and not found_backslash:
            found_backslash = True
        elif c == '"' and not found_backslash:
            found_backslash = False
            in_quote = not in_quote
        elif c == "#" and not in_quote:
            return line[:idx]
        else:
            found_backslash = False
    return line


def remove_comments(lines: typing.Iterable[str]) -> str:
    return "".join([remove_comments_from_line(line) + "\n" for line in lines])


def argparse_yes_no_flag(
    parser: typing.Union[argparse.ArgumentParser, argparse._ArgumentGroup],
    flag_name: str,
    on_prefix: str = "",
    off_prefix: str = "no-",
    default: typing.Optional[bool] = False,
    **kwargs: typing.Any,
) -> None:
    class FlagAction(argparse.Action):
        def __init__(self, option_strings, dest, nargs=None, **kwargs):
            super(FlagAction, self).__init__(option_strings, dest, nargs=0, **kwargs)

        def __call__(self, parser, namespace, values, option_string=None):
            setattr(
                namespace,
                self.dest,
                False if option_string.startswith(f"--{off_prefix}") else True,
            )

    parser.add_argument(
        f"--{on_prefix}{flag_name}",
        f"--{off_prefix}{flag_name}",
        dest=flag_name.replace("-", "_"),
        action=FlagAction,
        default=default,
        **kwargs,
    )


def unzip_apk(apk: str, destination_directory: str) -> None:
    with zipfile.ZipFile(apk) as z:
        z.extractall(destination_directory)


def extract_dex_number(dexfilename: str) -> int:
    m = re.search(r"(classes|.*-)(\d+)", basename(dexfilename))
    if m is None:
        raise Exception("Bad secondary dex name: " + dexfilename)
    return int(m.group(2))


def module_dex_glob(directory: str, store_name: str) -> typing.List[str]:
    """
    Return the dexes of an application module in dex order: classes.dex,
    classes2.dex, ...; <store_name>.dex, <store_name>2.dex, ...; or
    <prefix>-1.dex, <prefix>-2.dex, ...
    """

    def dex_number(path: str) -> int:
        m = re.fullmatch(
            rf"(?:classes|{re.escape(store_name)})(\d*)\.dex", basename(path)
        )
        if m is None:
            return extract_dex_number(path)
        return int(m.group(1)) if m.group(1) else 1

    dexes = sorted(glob.glob(join(directory, "*.dex")), key=dex_number)
    # Every unpacker names a module's dexes with one of the schemes above, so no
    # two of them get the same number. Equal numbers mean a directory that mixes
    # schemes, where nothing says which dex comes first; reject it rather than
    # guess.
    numbers = [dex_number(d) for d in dexes]
    if len(set(numbers)) != len(numbers):
        raise Exception(f"Ambiguous dex order: {dexes}")
    return dexes


def dex_glob(directory: str) -> typing.List[str]:
    """
    Return the dexes in a given directory, with the primary dex first.
    """
    primary = join(directory, "classes.dex")
    if not isfile(primary):
        raise Exception("No primary dex found")

    secondaries = [
        d for d in glob.glob(join(directory, "*.dex")) if not d.endswith("classes.dex")
    ]
    secondaries.sort(key=extract_dex_number)

    return [primary] + secondaries


def relocate_dexen_to_directories(
    root: str,
    dexpaths: typing.Iterable[str],
    should_copy: bool = False,
) -> typing.List[str]:
    """
    Move each dex file to its own directory within root and return a list of the
    new paths. Redex will operate on each dex and put the modified dex into the
    same directory.
    """
    res = []
    for idx, dexpath in enumerate(dexpaths):
        dexname = basename(dexpath)
        dirpath = join(root, "dex" + str(idx))
        os.mkdir(dirpath)
        if should_copy:
            shutil.copyfile(dexpath, os.path.join(dirpath, dexname))
            log(
                "relocate_dexen_to_directories creating copy: %s -> %s"
                % (dexpath, os.path.join(dirpath, dexname))
            )
        else:
            shutil.move(dexpath, dirpath)
        res.append(join(dirpath, dexname))

    return res


def ensure_libs_dir(libs_dir: str, sub_dir: str) -> str:
    """Ensures the base libs directory and the sub directory exist. Returns top
    most dir that was created.
    """
    if os.path.exists(libs_dir):
        os.mkdir(sub_dir)
        return sub_dir
    else:
        os.mkdir(libs_dir)
        os.mkdir(sub_dir)
        return libs_dir


def get_file_ext(file_name: str) -> str:
    return os.path.splitext(file_name)[1]


def _verify_dex(dex_file: str, cmd: str) -> bool:
    try:
        LOGGER.info("Verifying %s...", dex_file)

        res = subprocess.run(
            f"{cmd} '{dex_file}'", shell=True, text=False, capture_output=True
        )
        if res.returncode == 0:
            return True

        try:
            stderr_str = res.stderr.decode("utf-8")
        except BaseException:
            stderr_str = "<unable to decode, contains non-UTF8>"

    except BaseException as e:
        LOGGER.exception("Error for dex file %s", dex_file)
        stderr_str = f"{e}"

    LOGGER.error("Failed verification for %s:\n%s", dex_file, stderr_str)
    return False


def verify_dexes(dex_dir: str, cmd: str) -> None:
    timer = timeit.default_timer
    start = timer()

    dex_files = glob.glob(join(join(dex_dir, "**"), "*.dex"), recursive=True)
    if not dex_files:
        LOGGER.warning("Found no dex files to verify")
        return

    LOGGER.info("Verifying %d dex files...", len(dex_files))

    mp_context = (
        multiprocessing.get_context("fork")
        if sys.platform == "linux"
        else multiprocessing.get_context()
    )
    with mp_context.Pool() as pool:
        result = pool.starmap(
            _verify_dex,
            ((dex_file, cmd) for dex_file in dex_files),
        )

    assert all(result), "Some dex files failed to verify!"

    end = timer()
    LOGGER.debug("Dex verification finished in {:.2f} seconds".format(end - start))


try:
    # This is an xz that is built from source and provided via BUCK.
    from xz_for_python.xz import get_xz_bin_path
except ImportError:
    get_xz_bin_path = None


def get_xz_path() -> typing.Optional[str]:
    xz = None
    if get_xz_bin_path is not None:
        xz_bin_path = get_xz_bin_path()
        assert xz_bin_path is not None
        LOGGER.debug("Using provided xz")
        xz = xz_bin_path
    elif shutil.which("xz"):
        LOGGER.debug("Using command line xz")
        xz = "xz"
    return xz


_TIME_IT_DEPTH: int = 0


@contextmanager
def time_it(
    fmt: str, *args: typing.Any, **kwargs: typing.Any
) -> typing.Generator[int, None, None]:
    global _TIME_IT_DEPTH
    this_depth = _TIME_IT_DEPTH
    _TIME_IT_DEPTH += 1

    if "logger" in kwargs:
        logger_opt: typing.Optional[logging.Logger] = kwargs["logger"]
        if logger_opt:
            logger = logger_opt
        else:
            logger = logging.getLogger()
    else:
        logger = logging.getLogger()

    if "start" in kwargs:
        logger.info("-" * this_depth + kwargs["start"])

    timer = timeit.default_timer
    start_time = timer()
    try:
        yield 1  # Irrelevant
    finally:
        end_time = timer()
        logger.info("-" * this_depth + fmt.format(time=end_time - start_time), *args)

        _TIME_IT_DEPTH -= 1


# Look for a global LOGGER in the stack.
def time_it_logger(
    start_depth: int = 1, max_depth: int = 1
) -> typing.Optional[logging.Logger]:
    stack = inspect.stack()
    for i in range(start_depth, min(max_depth + 1, len(stack))):
        frame = stack[i].frame
        if hasattr(frame, "f_globals") and "LOGGER" in frame.f_globals:
            logger = frame.f_globals["LOGGER"]
            if isinstance(logger, logging.Logger):
                return logger

    return None


@contextmanager
def timed_scope(
    desc: str,
    timed_start: bool = True,
) -> typing.Generator[None, None, None]:
    # start_depth=2 skips this frame and contextlib's __enter__, so the LOGGER
    # lookup lands on the calling module.
    with time_it(
        f"{desc} took {{time:.2f}} seconds",
        logger=time_it_logger(start_depth=2, max_depth=5),
        **({"start": desc} if timed_start else {}),
    ):
        yield
