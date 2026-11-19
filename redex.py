#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# pyre-strict

import argparse
import enum
import errno
import glob
import json
import logging
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import typing
import zipfile
from dataclasses import dataclass
from os.path import abspath, dirname, exists, getsize, isdir, isfile, join
from shlex import quote

import pyredex.bintools as bintools
import pyredex.logger as logger
from pyredex.packer import compress_entries, CompressionEntry, CompressionLevel
from pyredex.unpacker import (
    LibraryManager,
    unpack_tar_xz,
    UnpackManager,
    ZipManager,
    ZipReset,
)
from pyredex.utils import (
    add_android_sdk_path,
    add_tool_override,
    argparse_yes_no_flag,
    dex_glob,
    find_zipalign,
    get_android_sdk_path,
    get_file_ext,
    make_temp_dir,
    omit_sdk_tool_discovery,
    relocate_dexen_to_directories,
    remove_comments,
    sign_apk,
    timed_scope,
    verify_dexes,
    with_temp_cleanup,
)


IS_WINDOWS: bool = os.name == "nt"
LOGGER: logging.Logger = logging.getLogger("redex")  # Don't want __main__


# Pyre helper.
T = typing.TypeVar("T")


def _assert_val(input: typing.Optional[T]) -> T:
    assert input is not None
    return input


def pgize(name: str) -> str:
    return name.strip()[1:][:-1].replace("/", ".")


def dbg_prefix(dbg: str, src_root: typing.Optional[str] = None) -> typing.List[str]:
    """Return a debugger command prefix.

    `dbg` is either "gdb" or "lldb", indicating which debugger to invoke.
    `src_root` is an optional parameter that indicates the root directory that
        all references to source files in debug information is relative to.

    Returns a list of strings, which when prefixed onto a shell command
        invocation will run that shell command under the debugger.
    """
    assert dbg in ["gdb", "lldb"]

    cmd = [dbg]
    if src_root is not None:
        if dbg == "gdb":
            cmd += ["-ex", quote("directory %s" % src_root)]
        elif dbg == "lldb":
            cmd += ["-o", f"""'settings set target.source-map "." {quote(src_root)}'"""]

            # This makes assumptions about buck-out... I couldn't find an easy
            # way to just get the config file beside this script...
            dir_name = dirname(abspath(__file__))
            dir_name = dirname(dir_name)
            lldbinit_file = dir_name + "/.lldbinit/.lldbinit"
            if isfile(lldbinit_file):
                cmd += ["-o", f"'command source {quote(lldbinit_file)}'"]

    DBG_END = {"gdb": "--args", "lldb": "--"}
    cmd.append(DBG_END[dbg])

    return cmd


def write_debugger_command(
    dbg: str, src_root: typing.Optional[str], args: typing.Iterable[str]
) -> str:
    """Write out a shell script that allows us to rerun redex-all under a debugger.

    The choice of debugger is governed by `dbg` which can be either "gdb" or "lldb".
    """
    assert not IS_WINDOWS  # It's a Linux/Mac script...
    fd, script_name = tempfile.mkstemp(suffix=".sh", prefix="redex-{}-".format(dbg))

    # Parametrise redex binary.
    args = [quote(a) for a in args]
    redex_binary = args[0]
    args[0] = '"$REDEX_BINARY"'

    with os.fdopen(fd, "w") as f:
        f.write("#! /usr/bin/env bash\n")
        f.write('REDEX_BINARY="${REDEX_BINARY:-%s}"\n' % redex_binary)
        f.write("cd %s || exit\n" % quote(os.getcwd()))
        f.write(" ".join(dbg_prefix(dbg, src_root)))
        f.write(" ")
        f.write(" ".join(args))
        if not IS_WINDOWS:
            os.fchmod(fd, 0o775)  # This is unsupported on windows.

    return script_name


def find_redex_binary(redex_binary: typing.Optional[str]) -> typing.Optional[str]:
    redex_binary = redex_binary or shutil.which("redex-all")
    if redex_binary is not None:
        return redex_binary

    # __file__ can be /path/fb-redex.pex/redex.pyc
    dir_name = dirname(abspath(__file__))
    while not isdir(dir_name):
        dir_name = dirname(dir_name)

    bundled_binary = join(dir_name, "redex-all")
    if isfile(bundled_binary):
        return bundled_binary
    return None


def add_extra_environment_args(env: typing.Dict[str, str]) -> None:
    # If we haven't set MALLOC_CONF but we have requested to profile the memory
    # of a specific pass, set some reasonable defaults
    if "MALLOC_PROFILE_PASS" in env and "MALLOC_CONF" not in env:
        env["MALLOC_CONF"] = (
            "prof:true,prof_prefix:jeprof.out,prof_gdump:true,prof_active:false"
        )

    # If we haven't set MALLOC_CONF, tune MALLOC_CONF for better perf
    if "MALLOC_CONF" not in env:
        env["MALLOC_CONF"] = "background_thread:true,metadata_thp:always,thp:always"


def get_stop_pass_idx(passes_list: typing.Iterable[str], pass_name_and_num: str) -> int:
    # Get the stop position
    # pass_name_and num may be "MyPass#0", "MyPass#3" or "MyPass"
    pass_name = pass_name_and_num
    pass_order = 0
    if "#" in pass_name_and_num:
        pass_name, pass_order = pass_name_and_num.split("#", 1)
        try:
            pass_order = int(pass_order)
        except ValueError:
            sys.exit(
                "Invalid stop-pass %s, should be in 'SomePass(#num)'"
                % pass_name_and_num
            )
    cur_order = 0
    for _idx, _name in enumerate(passes_list):
        if _name == pass_name:
            if cur_order == pass_order:
                return _idx
            else:
                cur_order += 1
    sys.exit(
        "Invalid stop-pass %s. %d %s in passes_list"
        % (pass_name_and_num, cur_order, pass_name)
    )


class ExceptionMessageFormatter:
    def format_rerun_message(self, gdb_script_name: str, lldb_script_name: str) -> str:
        return "You can re-run it under gdb by running {} or under lldb by running {}".format(
            gdb_script_name, lldb_script_name
        )

    def format_message(
        self,
        err_out: typing.List[str],
        default_error_msg: str,
        gdb_script_name: str,
        lldb_script_name: str,
    ) -> str:
        return "{} {}".format(
            default_error_msg,
            self.format_rerun_message(gdb_script_name, lldb_script_name),
        )


class DexenSnapshot(object):
    def __init__(self, dex_dir: str) -> None:
        self.files_and_sizes: typing.Dict[str, int] = {
            dexpath: os.path.getsize(dexpath) for dexpath in dex_glob(dex_dir)
        }

    def equals(self, other: "DexenSnapshot") -> bool:
        return self.files_and_sizes == other.files_and_sizes


@dataclass(slots=True)
class State:
    args: argparse.Namespace
    config_dict: typing.Dict[str, typing.Any]
    debugger: typing.Optional[str]
    dex_dir: str
    dexen: typing.List[str]
    extracted_apk_dir: typing.Optional[str]
    stop_pass_idx: int
    lib_manager: typing.Optional[LibraryManager]
    unpack_manager: typing.Optional[UnpackManager]
    zip_manager: typing.Optional[ZipManager]
    dexen_initial_state: typing.Optional[DexenSnapshot]


class RedexRunException(Exception):
    def __init__(
        self,
        msg: str,
        return_code: int,
        abort_error: typing.Optional[str],
        symbolized: typing.Optional[typing.List[str]],
    ) -> None:
        super().__init__(msg, return_code, abort_error, symbolized)
        self.msg = msg
        self.return_code = return_code
        self.abort_error = abort_error
        self.symbolized = symbolized

    def __str__(self) -> str:
        return self.msg


def run_redex_binary(
    state: State,
    exception_formatter: ExceptionMessageFormatter,
    output_line_handler: typing.Optional[typing.Callable[[str], str]],
) -> None:
    state.args.redex_binary = find_redex_binary(state.args.redex_binary)
    if state.args.redex_binary is None:
        sys.exit("redex-all was not found")
    if not isfile(state.args.redex_binary) or not os.access(
        state.args.redex_binary, os.X_OK
    ):
        sys.exit(
            "redex-all was not found or is not executable: " + state.args.redex_binary
        )
    LOGGER.debug("Running redex binary at %s", state.args.redex_binary)

    args: typing.List[str] = [state.args.redex_binary]

    args += (
        (["--dex-files"] + state.args.dex_files)
        if state.args.dex_files
        else ["--apkdir", _assert_val(state.extracted_apk_dir)]
    )
    args += ["--outdir", state.dex_dir]

    if state.args.cmd_prefix is not None:
        args = shlex.split(state.args.cmd_prefix) + args

    if state.args.config:
        args += ["--config", state.args.config]

    if state.args.verify_none_mode or state.config_dict.get("verify_none_mode"):
        args += ["--verify-none-mode"]

    if state.args.is_art_build:
        args += ["--is-art-build"]

    if state.args.disable_dex_hasher:
        args += ["--disable-dex-hasher"]

    if state.args.enable_instrument_pass or state.config_dict.get(
        "enable_instrument_pass"
    ):
        args += ["--enable-instrument-pass"]

    if state.args.warn:
        args += ["--warn", state.args.warn]
    args += ["--proguard-config=" + x for x in state.args.proguard_configs]
    if state.args.proguard_map:
        args += ["-Sproguard_map=" + state.args.proguard_map]

    args += ["--jarpath=" + x for x in state.args.jarpaths]
    if state.args.printseeds:
        args += ["--printseeds=" + state.args.printseeds]
    if state.args.used_js_assets:
        args += ["--used-js-assets=" + x for x in state.args.used_js_assets]
    if state.args.arch:
        args += ["--arch=" + state.args.arch]
    if state.args.jni_summary:
        args += ["--jni-summary=" + state.args.jni_summary]
    args += ["-S" + x for x in state.args.passthru]
    args += ["-J" + x for x in state.args.passthru_json]

    if state.args.assert_abort:
        args += ["--assert-abort", state.args.assert_abort]
    if state.args.assert_abort_thread:
        args += ["--assert-abort-thread", state.args.assert_abort_thread]
    if state.args.chrome_trace:
        args += ["--chrome-trace"]

    args += state.dexen

    # Stop before a pass and output intermediate dex and IR meta data.
    if state.stop_pass_idx != -1:
        args += [
            "--stop-pass",
            str(state.stop_pass_idx),
            "--output-ir",
            state.args.output_ir,
        ]

    if state.args.redex_extra_args:
        args += [
            extra_arg
            for extra_arg_unsplit in state.args.redex_extra_args
            for extra_arg in shlex.split(extra_arg_unsplit)
        ]

    debugger = state.debugger
    prefix: typing.List[str] = (
        dbg_prefix(debugger, state.args.debug_source_root)
        if debugger is not None
        else []
    )

    if state.args.debug:
        print("cd %s && %s" % (os.getcwd(), " ".join(prefix + list(map(quote, args)))))
        sys.exit()

    env: typing.Dict[str, str] = os.environ.copy()
    if state.args.quiet:
        # Remove TRACE if it exists.
        env.pop("TRACE", None)
    else:
        # Check whether TRACE is set. If not, use "TIME:1,PM:1".
        if "TRACE" not in env:
            env["TRACE"] = "TIME:1,PM:1"

    env = logger.setup_trace_for_child(env)
    logger.flush()

    add_extra_environment_args(env)

    def run() -> None:
        with bintools.SigIntHandler() as sigint_handler:
            trace_fp = logger.get_trace_file()
            pass_fds = [trace_fp.fileno()] if trace_fp is not sys.stderr else []

            with tempfile.TemporaryDirectory() as tmp_dir:
                crash_file = join(tmp_dir, "crash.txt")
                crash_args = ["--crash-file", crash_file]

                proc, handler = bintools.run_and_stream_stderr(
                    prefix + args + crash_args, env, pass_fds
                )
                sigint_handler.set_started(proc)

                returncode, err_out = handler(output_line_handler)

                sigint_handler.set_postprocessing()

                if returncode == 0:
                    return

                # Check for crash traces.
                # Note: no need for store-logs, as this has failed anyways.
                symbolized = bintools.maybe_addr2line(crash_file)

                if symbolized:
                    sys.stderr.write("\n")
                    sys.stderr.write("\n".join(symbolized))
                    sys.stderr.write("\n")
                elif exists(crash_file) and getsize(crash_file) > 0:
                    with open(crash_file) as f:
                        sys.stderr.write(f.read())
                sys.stderr.flush()

            abort_error = None
            if returncode == -6:  # SIGABRT
                abort_error = bintools.find_abort_error(err_out)

            default_error_msg = "redex-all crashed with exit code {}!{}".format(
                returncode, "\n" + abort_error if abort_error else ""
            )
            if IS_WINDOWS:
                raise RuntimeError(default_error_msg)

            gdb_script_name = write_debugger_command(
                "gdb", state.args.debug_source_root, args
            )
            lldb_script_name = write_debugger_command(
                "lldb", state.args.debug_source_root, args
            )
            msg = exception_formatter.format_message(
                err_out,
                default_error_msg,
                gdb_script_name,
                lldb_script_name,
            )
            raise RedexRunException(msg, returncode, abort_error, symbolized)

    # Our CI system occasionally fails because it is trying to write the
    # redex-all binary when this tries to run.  This shouldn't happen, and
    # might be caused by a JVM bug.  Anyways, let's retry and hope it stops.
    for i in range(5):
        try:
            run()
            break
        except OSError as err:
            if err.errno == errno.ETXTBSY and i < 4:
                continue
            raise err


class PageAlignment(enum.Enum):
    NONE = ()
    PAGE_4KB = ("-p",)
    PAGE_16KB = ("-P", "16")

    @classmethod
    def from_args(cls, page_align: bool, page_align_16kb: bool) -> "PageAlignment":
        if page_align_16kb:
            return cls.PAGE_16KB
        if page_align:
            return cls.PAGE_4KB
        return cls.NONE


def zipalign(
    unaligned_apk_path: str,
    output_apk_path: str,
    ignore_zipalign: bool,
    page_align: PageAlignment = PageAlignment.NONE,
) -> None:
    # Align zip and optionally perform good compression.
    try:
        zipalign = [
            find_zipalign(),
            *page_align.value,
            "4",
            unaligned_apk_path,
            output_apk_path,
        ]

        p = subprocess.Popen(zipalign, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        out, _ = p.communicate()
        if p.returncode == 0:
            os.remove(unaligned_apk_path)
            return
        out_str = out.decode(sys.getfilesystemencoding())
        raise RuntimeError("Failed to execute zipalign, output: {}".format(out_str))
    except OSError as e:
        if e.errno == errno.ENOENT:
            print("Couldn't find zipalign. See README.md to resolve this.")
        if not ignore_zipalign:
            raise e
        shutil.copy(unaligned_apk_path, output_apk_path)
    except BaseException:
        if not ignore_zipalign:
            raise
        shutil.copy(unaligned_apk_path, output_apk_path)
    os.remove(unaligned_apk_path)


@dataclass
class SigningConfig:
    keystore: str
    keyalias: str
    keypass: str


def extract_signing_args(
    args: argparse.Namespace,
    fail_on_error: bool = True,
) -> typing.Optional[SigningConfig]:
    def maybe_fail(msg: str) -> typing.Optional[SigningConfig]:
        if fail_on_error:
            raise argparse.ArgumentTypeError(msg)
        else:
            return None

    keystore = args.keystore  # For pyre
    keyalias = args.keyalias  # For pyre
    keypass = args.keypass  # For pyre
    keystore_properties = args.keystore_properties  # For pyre

    if keystore_properties:
        if keyalias or keypass:
            return maybe_fail(
                "Cannot specify --keystore-properties and --keyalias/--keypass"
            )
        if not isfile(keystore_properties):
            return maybe_fail(
                f'Keystore properties path "{keystore_properties}" is invalid.'
            )
        with open(keystore_properties) as f:
            entries = {
                entry[0]: entry[1]
                for entry in (
                    line.strip().split("=")
                    for line in f
                    if not line.startswith("#") and "=" in line
                )
            }
        if "key.alias" not in entries:
            return maybe_fail(
                f'Keystore properties path "{keystore_properties}" does not contain "key.alias"'
            )
        keyalias = entries["key.alias"]
        if "key.alias.password" not in entries:
            return maybe_fail(
                f'Keystore properties path "{keystore_properties}" does not contain "key.alias.password"'
            )
        keypass = entries["key.alias.password"]
    else:
        if not keyalias:
            return maybe_fail("Requires --keyalias argument")

        if not keypass:
            return maybe_fail("Requires --keypass argument")

    if not keystore:
        return maybe_fail("Requires --keystore argument")
    if not isfile(keystore):
        return maybe_fail(f'Keystore path "{keystore}" is invalid.')

    return SigningConfig(
        keystore=keystore,
        keyalias=keyalias,
        keypass=keypass,
    )


def align_and_sign_output_apk(
    unaligned_apk_path: str,
    output_apk_path: str,
    reset_timestamps: bool,
    sign: bool,
    sign_v4: typing.Optional[bool],
    signing_config: typing.Optional[SigningConfig],
    ignore_zipalign: bool,
    ignore_apksigner: bool,
    page_align: PageAlignment = PageAlignment.NONE,
) -> None:
    if isfile(output_apk_path):
        os.remove(output_apk_path)

    try:
        os.makedirs(dirname(output_apk_path))
    except OSError as e:
        if e.errno != errno.EEXIST:
            raise

    zipalign(unaligned_apk_path, output_apk_path, ignore_zipalign, page_align)

    if reset_timestamps:
        ZipReset.reset_file(output_apk_path)

    # Add new signature
    if sign:
        assert signing_config
        sign_apk(
            sign_v4,
            signing_config.keystore,
            signing_config.keypass,
            signing_config.keyalias,
            output_apk_path,
            ignore_apksigner,
        )


def copy_file_to_out_dir(
    tmp: str, apk_output_path: str, name: str, human_name: str, out_name: str
) -> None:
    output_dir = os.path.dirname(apk_output_path)
    output_path = os.path.join(output_dir, out_name)
    tmp_path = tmp + "/" + name
    if os.path.isfile(tmp_path):
        shutil.copy2(tmp_path, output_path)
        LOGGER.debug("Copying " + human_name + " map to output_dir: " + output_path)
    else:
        LOGGER.debug("Skipping " + human_name + " copy, since no file found to copy")


def copy_all_file_to_out_dir(
    tmp: str, apk_output_path: str, ext: str, human_name: str
) -> None:
    tmp_path = tmp + "/" + ext
    for file in glob.glob(tmp_path):
        filename = os.path.basename(file)
        copy_file_to_out_dir(
            tmp, apk_output_path, filename, human_name + " " + filename, filename
        )


def validate_args(args: argparse.Namespace) -> None:
    if args.sign:
        # This will raise errors if necessary.
        extract_signing_args(args)

    if not args.unpack_only:
        args.redex_binary = find_redex_binary(args.redex_binary)
        if not args.redex_binary:
            raise argparse.ArgumentTypeError("Requires --redex-binary argument")
        if not args.config:
            raise argparse.ArgumentTypeError("Requires --config argument")


def arg_parser() -> argparse.ArgumentParser:
    description = """
Given an APK, produce a better APK!

"""
    parser = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter, description=description
    )

    parser.add_argument("input_apk", nargs="?", help="Input APK file")
    parser.add_argument(
        "-o",
        "--out",
        nargs="?",
        type=os.path.realpath,
        default="redex-out.apk",
        help="Output APK file name (defaults to redex-out.apk)",
    )
    parser.add_argument(
        "-j",
        "--jarpath",
        dest="jarpaths",
        action="append",
        default=[],
        help="Path to dependent library jar file",
    )

    parser.add_argument("--redex-binary", help="Path to redex binary")

    parser.add_argument("-c", "--config", help="Configuration file")

    signing_group = parser.add_argument_group("Signing arguments")
    argparse_yes_no_flag(signing_group, "sign", help="Sign the apk after optimizing it")
    argparse_yes_no_flag(
        signing_group, "sign-v4", default=None, help="Sign the apk with v4 signing"
    )
    signing_group.add_argument("-s", "--keystore")
    signing_group.add_argument("--keystore-properties")
    signing_group.add_argument("-a", "--keyalias")
    signing_group.add_argument("-p", "--keypass")

    parser.add_argument(
        "-u",
        "--unpack-only",
        action="store_true",
        help="Unpack the apk and print the unpacked directories, don't "
        "run any redex passes or repack the apk",
    )

    parser.add_argument(
        "--unpack-dest",
        nargs=1,
        help="Specify the base name of the destination directories; works with -u",
    )

    parser.add_argument("-w", "--warn", nargs="?", help="Control verbosity of warnings")

    parser.add_argument(
        "-d",
        "--debug",
        action="store_true",
        help="Unpack the apk and print the redex command line to run",
    )

    parser.add_argument(
        "--dev", action="store_true", help="Optimize for development speed"
    )

    parser.add_argument(
        "--fast-repackage",
        action="store_true",
        help="Repackage xz-compressed secondary dex stores with xz level 0 instead "
        "of 9. Unlike --dev, this changes nothing else.",
    )

    parser.add_argument(
        "-m",
        "--proguard-map",
        nargs="?",
        help="Path to proguard mapping.txt for deobfuscating names",
    )

    parser.add_argument("--printseeds", nargs="?", help="File to print seeds to")

    parser.add_argument(
        "--used-js-assets",
        action="append",
        default=[],
        help="A JSON file (or files) containing a list of resources used by JS",
    )

    parser.add_argument(
        "-P",
        "--proguard-config",
        dest="proguard_configs",
        action="append",
        default=[],
        help="Path to proguard config",
    )

    parser.add_argument(
        "-k",
        "--keep",
        nargs="?",
        help="[deprecated] Path to file containing classes to keep",
    )

    parser.add_argument(
        "-A",
        "--arch",
        nargs="?",
        help='Architecture; one of arm/armv7/arm64/x86_64/x86"',
    )

    parser.add_argument(
        "-S",
        dest="passthru",
        action="append",
        default=[],
        help="Arguments passed through to redex",
    )
    parser.add_argument(
        "-J",
        dest="passthru_json",
        action="append",
        default=[],
        help="JSON-formatted arguments passed through to redex",
    )

    parser.add_argument("--lldb", action="store_true", help="Run redex binary in lldb")
    parser.add_argument("--gdb", action="store_true", help="Run redex binary in gdb")
    parser.add_argument(
        "--ignore-zipalign", action="store_true", help="Ignore if zipalign is not found"
    )
    parser.add_argument(
        "--ignore-apksigner",
        action="store_true",
        help="Ignore if apksigner is not found",
    )
    parser.add_argument(
        "--verify-none-mode",
        action="store_true",
        help="Enable verify-none mode on redex",
    )
    parser.add_argument(
        "--enable-instrument-pass",
        action="store_true",
        help="Enable InstrumentPass if any",
    )
    parser.add_argument(
        "--is-art-build",
        action="store_true",
        help="States that this is an art only build",
    )
    parser.add_argument(
        "--disable-dex-hasher", action="store_true", help="Disable DexHasher"
    )
    parser.add_argument(
        "--page-align-libs",
        action="store_true",
        help="Preserve 4k page alignment for uncompressed libs",
    )
    parser.add_argument(
        "--page-align-libs-16kb",
        action="store_true",
        help="Use 16KB page alignment for uncompressed libs (required for Android 15+ devices)",
    )

    parser.add_argument(
        "--side-effect-summaries", help="Side effect information for external methods"
    )

    parser.add_argument(
        "--escape-summaries", help="Escape information for external methods"
    )

    parser.add_argument(
        "--stop-pass",
        default="",
        help="Stop before a pass and dump intermediate dex and IR meta data to a directory",
    )
    parser.add_argument(
        "--output-ir",
        default="",
        help="Stop before stop_pass and dump intermediate dex and IR meta data to output_ir folder",
    )
    parser.add_argument(
        "--debug-source-root",
        default=None,
        nargs="?",
        help="Root directory that all references to source files in debug information is given relative to.",
    )

    parser.add_argument(
        "--always-clean-up",
        action="store_true",
        help="Clean up temporaries even under failure",
    )

    parser.add_argument("--cmd-prefix", type=str, help="Prefix redex-all with")

    parser.add_argument(
        "--reset-zip-timestamps",
        action="store_true",
        help="Reset zip timestamps for deterministic output",
    )

    parser.add_argument(
        "-q",
        "--quiet",
        action="store_true",
        help="Do not be verbose, and override TRACE.",
    )

    parser.add_argument("--android-sdk-path", type=str, help="Path to Android SDK")

    parser.add_argument(
        "--suppress-android-jar-check",
        action="store_true",
        help="Do not look for an `android.jar` in the jar paths",
    )

    parser.add_argument(
        "--omit-sdk-tool-discovery",
        action="store_true",
        help="Do not look attempt to search for SDK tools via path construction. Use the provided tool path overrides or the buck defaults",
    )

    parser.add_argument("--addr2line", help="Path to addr2line for crash symbolication")

    parser.add_argument(
        "--log-level",
        default="info",
        help="Specify the python logging level",
    )
    parser.add_argument(
        "--store-logs", action="store_true", help="Store all logs as meta"
    )

    parser.add_argument(
        "--packed-profiles",
        type=str,
        help="Path to packed profiles (expects tar.xz)",
    )

    parser.add_argument(
        "--baseline-profile-config",
        type=str,
        help="Baseline profile config list",
    )

    parser.add_argument(
        "--jni-summary",
        default=None,
        type=str,
        help="Path to JNI summary directory of json files.",
    )

    parser.add_argument(
        "--verify-dexes", type=str, help="Verify dex files with the supplied command"
    )

    parser.add_argument(
        "--deep-data-enabled-interactions",
        default=None,
        action="extend",
        nargs="+",
        help="Override deep data enabled interactions",
    )

    parser.add_argument(
        "--class-frequencies",
        type=str,
        help="Path to a zipped file containing class frequencies for different interactions (expects .zip)",
    )

    parser.add_argument("--assert-abort", type=str, help="For testing only!")
    parser.add_argument("--assert-abort-thread", type=str, help="For testing only!")

    # Manual tool paths.

    # Must be subclassed.
    class ToolAction(argparse.Action):
        def __init__(
            self, tool_name, option_strings, dest, nargs=None, type=None, **kwargs
        ):
            if nargs is not None:
                raise ValueError("nargs not allowed")
            if type is not None:
                raise ValueError("type not allowed")
            super().__init__(option_strings, dest, type=str, **kwargs)
            self.tool_name = tool_name

        def __call__(self, parser, namespace, values, option_string=None):
            if values is not None:
                add_tool_override(self.tool_name, values)

    class ZipAlignToolAction(ToolAction):
        def __init__(self, **kwargs):
            super().__init__("zipalign", **kwargs)

    parser.add_argument(
        "--zipalign-path",
        default=None,
        action=ZipAlignToolAction,
        help="Path to zipalign executable.",
    )

    class ApkSignerToolAction(ToolAction):
        def __init__(self, *args, **kwargs):
            super().__init__("apksigner", *args, **kwargs)

    parser.add_argument(
        "--apksigner-path",
        default=None,
        action=ApkSignerToolAction,
        help="Path to apksigner executable.",
    )

    # Passthrough mode.
    parser.add_argument("--outdir", type=str)
    parser.add_argument("--dex-files", nargs="+", default=[])

    parser.add_argument("--trace", type=str)
    parser.add_argument("--trace-file", type=str)
    # Relevant options to TraceClassAfterEachPass
    parser.add_argument("--trace-class-name", type=str)
    parser.add_argument("--trace-method-name", type=str)
    parser.add_argument("--after-pass-trace-file", type=str)
    parser.add_argument(
        "--chrome-trace",
        action="store_true",
        default=False,
        help="Write a Chrome Trace Event JSON file (redex-chrome-trace.json) to the "
        "meta output directory for visualization in Perfetto or chrome://tracing.",
    )

    # Extra args for redex binary.
    parser.add_argument("--redex-extra-args", action="append", default=[])

    return parser


def _has_android_library_jars(pg_file: str) -> bool:
    # We do not tokenize properly here. Minimum effort.
    def _gen() -> typing.Generator[str, None, None]:
        with open(pg_file, "r") as f:
            for line in f:
                yield line.strip()

    gen = _gen()
    for line in gen:
        if line == "-libraryjars":
            line = next(gen, "a")
            parts = line.split(":")
            for p in parts:
                if p.endswith("android.jar"):
                    return True
    return False


def _check_android_sdk_jar(args: argparse.Namespace) -> None:
    if args.suppress_android_jar_check:
        LOGGER.debug("No SDK jar check done")
        return

    for jarpath in args.jarpaths:
        if jarpath.endswith("android.jar"):
            LOGGER.debug("Found an SDK-looking jar: %s", jarpath)
            return

    for pg_config in args.proguard_configs:
        if _has_android_library_jars(pg_config):
            LOGGER.debug("Found an SDK-looking jar in PG file %s", pg_config)
            return

    # Check whether we can find and add one.
    LOGGER.info(
        "No SDK jar found. If the detection is wrong, add `--suppress-android-jar-check`."
    )
    if args.omit_sdk_tool_discovery:
        raise RuntimeError(
            "SDK tool discovery explicitly disabled, not attempting to locate SDK jar via SDK path. Failing due to no SDK jar provided."
        )

    LOGGER.info("Attempting to find an SDK-looking jar via SDK path")

    try:
        sdk_path = get_android_sdk_path()
        LOGGER.debug("SDK path is %s", sdk_path)
        platforms = join(sdk_path, "platforms")
        if not os.path.exists(platforms):
            raise RuntimeError("platforms directory does not exist")
        VERSION_REGEXP = r"android-(\d+)"
        version = max(
            (
                -1,
                *[
                    int(m.group(1))
                    for d in os.listdir(platforms)
                    for m in [re.match(VERSION_REGEXP, d)]
                    if m
                ],
            ),
        )
        if version == -1:
            raise RuntimeError(f"No android jar directories found in {platforms}")
        jar_path = join(platforms, f"android-{version}", "android.jar")
        if not os.path.exists(jar_path):
            raise RuntimeError(f"{jar_path} not found")
        LOGGER.info("Adding SDK jar path %s", jar_path)
        args.jarpaths.append(jar_path)
    except BaseException as e:
        LOGGER.warning("Could not find an SDK jar: %s", e)


def _has_config_val(args: argparse.Namespace, path: typing.Iterable[str]) -> bool:
    try:
        with open(args.config, "r") as f:
            json_obj = json.load(f)
        for item in path:
            if item not in json_obj:
                LOGGER.debug("Did not find %s in %s", item, json_obj)
                return False
            json_obj = json_obj[item]
        return True
    except BaseException as e:
        LOGGER.error("%s", e)
        return False


def _check_shrinker_heuristics(args: argparse.Namespace) -> None:
    arg_template = "inliner.reg_alloc_random_forest="
    for arg in args.passthru:
        if arg.startswith(arg_template):
            return

    if _has_config_val(args, ["inliner", "reg_alloc_random_forest"]):
        return

    # Nothing found, check whether we have files embedded
    LOGGER.info("No shrinking heuristic found, searching for default.")
    try:
        from generated_shrinker_regalloc_heuristics import SHRINKER_HEURISTICS_FILE

        LOGGER.info("Found embedded shrinker heuristics")
        tmp_dir = make_temp_dir("shrinker_heuristics")
        filename = os.path.join(tmp_dir, "shrinker.forest")
        LOGGER.debug("Writing shrinker heuristics to %s", filename)
        with open(filename, "wb") as f:
            f.write(SHRINKER_HEURISTICS_FILE)
        arg = arg_template + filename
        args.passthru.append(arg)
    except ImportError:
        LOGGER.info("No embedded files, please add manually!")


def _check_android_sdk_api(args: argparse.Namespace) -> None:
    arg_template = "android_sdk_api_{level}_file="
    arg_re = re.compile("^" + arg_template.format(level="(\\d+)"))
    for arg in args.passthru:
        if arg_re.match(arg):
            return

    # Nothing found, check whether we have files embedded
    LOGGER.info("No android_sdk_api_XX_file parameters found.")
    try:
        import generated_apilevels as ga

        levels = ga.get_api_levels()
        LOGGER.info("Found embedded API levels: %s", levels)
        api_dir = make_temp_dir("api_levels")
        LOGGER.debug("Writing API level files to %s", api_dir)
        for level in levels:
            blob = ga.get_api_level_file(level)
            filename = os.path.join(api_dir, f"framework_classes_api_{level}.txt")
            with open(filename, "wb") as f:
                f.write(blob)
            arg = arg_template.format(level=level) + filename
            args.passthru.append(arg)
    except ImportError:
        LOGGER.warning("No embedded files, please add manually!")


def _handle_baseline_profiles(args: argparse.Namespace) -> None:
    if args.baseline_profile_config:
        args.passthru.append(f"baseline_profile_config={args.baseline_profile_config}")


# Returns a tuple of baseline profile interactions
# The first element is all interactions
# The second element is default interactions
def _get_baseline_profile_interactions(
    args: argparse.Namespace,
) -> typing.Tuple[typing.Set[str], typing.Set[str]]:
    if not args.baseline_profile_config:
        return set(), set()
    with open(
        os.path.join(args.baseline_profile_config, "baseline_profile_configs.json")
    ) as f:
        json_config = json.load(f)
        LOGGER.error(json_config)
        return {
            interaction_id
            for _, config in json_config.items()
            for interaction_id in config.get("deep_data_interaction_config", {})
        }, set(json_config["default"].get("deep_data_interaction_config", {}).keys())


def _handle_profiles(
    args: argparse.Namespace, dd_enabled_interactions: typing.List[str]
) -> None:
    if not args.packed_profiles:
        return

    with timed_scope("Unpacking Profiles"):
        directory = make_temp_dir(".redex_profiles", False)
        unpack_tar_xz(args.packed_profiles, directory)

        baseline_profile_interactions, default_baseline_profile_interactions = (
            _get_baseline_profile_interactions(args)
        )

        all_method_profiles_paths = [
            f'"{f.path}"'
            for f in os.scandir(directory)
            if f.is_file() and ("method_stats" in f.name or "agg_stats" in f.name)
        ]

        method_profiles_paths: typing.List[str]
        if len(dd_enabled_interactions) > 0:
            method_profiles_paths = [
                mpp
                for mpp in all_method_profiles_paths
                if any(f"_{i}_" in mpp for i in dd_enabled_interactions)
                or any(f"_{i}_" in mpp for i in default_baseline_profile_interactions)
            ]
        else:
            method_profiles_paths = all_method_profiles_paths.copy()

        variant_method_profiles_paths = [
            mpp
            for mpp in all_method_profiles_paths
            if any(f"_{i}_" in mpp for i in baseline_profile_interactions)
            and mpp not in method_profiles_paths
        ]

        # Create input for method profiles.
        method_profiles_str = ", ".join(method_profiles_paths)
        if method_profiles_str:
            LOGGER.debug("Found method profiles: %s", method_profiles_str)
            args.passthru_json.append(f"agg_method_stats_files=[{method_profiles_str}]")
        else:
            LOGGER.info("No method profiles found in %s", args.packed_profiles)

        # Create input for variant method profiles.
        variant_method_profiles_str = ", ".join(variant_method_profiles_paths)
        if variant_method_profiles_str:
            LOGGER.debug(
                "Found variant method profiles: %s", variant_method_profiles_str
            )
            args.passthru_json.append(
                f"baseline_profile_agg_method_stats_files=[{variant_method_profiles_str}]"
            )
        else:
            LOGGER.info("No variant method profiles found in %s", args.packed_profiles)

        # Create input for basic blocks.

        block_profiles_paths = (
            f"{f.path}"
            for f in os.scandir(directory)
            if f.is_file() and f.name.startswith("block_profiles_")
        )

        if len(dd_enabled_interactions) > 0:
            block_profiles_paths = [
                bpp
                for bpp in block_profiles_paths
                if any([f"_{i}_" in bpp for i in dd_enabled_interactions])
            ]

        join_str = ";" if IS_WINDOWS else ":"
        block_profiles_str = join_str.join(block_profiles_paths)
        if block_profiles_str:
            LOGGER.debug("Found block profiles: %s", block_profiles_str)
            # Assume there's at most one.
            args.passthru.append(
                f"InsertSourceBlocksPass.profile_files={block_profiles_str}"
            )
        else:
            LOGGER.info("No block profiles found in %s", args.packed_profiles)

        coldstart_method_ordering_str = join_str.join(
            f"{f.path}"
            for f in os.scandir(directory)
            if f.is_file() and f.name.startswith("coldstart_method_ordering")
        )
        if coldstart_method_ordering_str:
            LOGGER.debug("Found coldstart ordering: %s", coldstart_method_ordering_str)
            # Assume there's at most one.
            args.passthru.append(
                f"coldstart_methods_file={coldstart_method_ordering_str}"
            )
        else:
            LOGGER.info("No coldstart ordering found in %s", args.packed_profiles)


def _handle_class_frequencies(args: argparse.Namespace) -> None:
    if not args.class_frequencies:
        return
    with timed_scope("Unpacking Class Frequencies"):
        class_freq_directory = make_temp_dir(".redex_class_frequencies", False)
        with zipfile.ZipFile(args.class_frequencies, "r") as class_freq_zip:
            class_freq_zip.extractall(path=class_freq_directory)

        join_str = ";" if IS_WINDOWS else ":"
        class_frequencies_str = join_str.join(
            f"{f.path}"
            for f in os.scandir(class_freq_directory)
            if f.is_file() and f.name.startswith("class_freqs")
        )
        if class_frequencies_str:
            LOGGER.debug("Found class_frequencies: %s", class_frequencies_str)
            # Assume there's at most one.
            args.passthru.append(f"class_frequencies={class_frequencies_str}")
        else:
            LOGGER.info("No class_frequencies found in %s", args.class_frequencies)


def prepare_redex(args: argparse.Namespace) -> State:
    LOGGER.debug("Preparing...")
    debug_mode = args.unpack_only or args.debug

    if args.android_sdk_path:
        add_android_sdk_path(args.android_sdk_path)

    if args.omit_sdk_tool_discovery:
        omit_sdk_tool_discovery()

    if args.addr2line:
        bintools.set_addr2line_path(args.addr2line)

    # avoid accidentally mixing up file formats since we now support
    # both apk files and Android bundle files
    file_ext = get_file_ext(args.input_apk)
    if not args.unpack_only:
        assert file_ext == get_file_ext(args.out), (
            'Input file extension ("'
            + file_ext
            + '") should be the same as output file extension ("'
            + get_file_ext(args.out)
            + '")'
        )

    extracted_apk_dir = None
    dex_dir = None
    if args.unpack_only and args.unpack_dest:
        if args.unpack_dest[0] == ".":
            # Use APK's name
            unpack_dir_basename = os.path.splitext(args.input_apk)[0]
        else:
            unpack_dir_basename = args.unpack_dest[0]
        extracted_apk_dir = unpack_dir_basename + ".redex_extracted_apk"
        dex_dir = unpack_dir_basename + ".redex_dexen"
        try:
            os.makedirs(extracted_apk_dir)
            os.makedirs(dex_dir)
            extracted_apk_dir = os.path.abspath(extracted_apk_dir)
            dex_dir = os.path.abspath(dex_dir)
        except OSError as e:
            if e.errno == errno.EEXIST:
                print("Error: destination directory already exists!")
                print("APK: " + extracted_apk_dir)
                print("DEX: " + dex_dir)
                sys.exit(1)
            raise e

    config = args.config
    binary = args.redex_binary
    LOGGER.debug("Using config %s", config if config is not None else "(default)")
    LOGGER.debug("Using binary %s", binary if binary is not None else "(default)")

    if args.unpack_only or config is None:
        config_dict = {}
    else:
        with open(config) as config_file:
            try:
                lines = config_file.readlines()
                config_dict = json.loads(remove_comments(lines))
            except ValueError:
                raise ValueError(
                    "Invalid JSON in ReDex config file: %s" % config_file.name
                )

    # stop_pass_idx >= 0 means need stop before a pass and dump intermediate result
    stop_pass_idx = -1
    if args.stop_pass:
        passes_list = config_dict.get("redex", {}).get("passes", [])
        stop_pass_idx = get_stop_pass_idx(passes_list, args.stop_pass)
        if not args.output_ir or isfile(args.output_ir):
            print("Error: output_ir should be a directory")
            sys.exit(1)
        try:
            os.makedirs(args.output_ir)
        except OSError as e:
            if e.errno != errno.EEXIST:
                raise e

    with timed_scope("Unpacking Redex input"):
        with timed_scope("Unpacking APK"):
            LOGGER.debug("Unpacking...")
            if not extracted_apk_dir:
                extracted_apk_dir = make_temp_dir(".redex_extracted_apk", debug_mode)

            directory = make_temp_dir(".redex_unaligned", False)
            unaligned_apk_path = join(directory, "redex-unaligned." + file_ext)
            zip_manager = ZipManager(
                args.input_apk, extracted_apk_dir, unaligned_apk_path
            )
            zip_manager.__enter__()

            if not dex_dir:
                dex_dir = make_temp_dir(".redex_dexen", debug_mode)

            is_bundle = isfile(join(extracted_apk_dir, "BundleConfig.pb"))
            unpack_manager = UnpackManager(
                args.input_apk,
                extracted_apk_dir,
                dex_dir,
                debug_mode=debug_mode,
                fast_repackage=args.dev or args.fast_repackage,
                reset_timestamps=args.reset_zip_timestamps or args.dev,
                is_bundle=is_bundle,
            )
            store_files = unpack_manager.__enter__()

            lib_manager = LibraryManager(extracted_apk_dir, is_bundle=is_bundle)
            lib_manager.__enter__()

            if args.unpack_only:
                print("APK: " + extracted_apk_dir)
                print("DEX: " + dex_dir)
                sys.exit()

        # Unpack profiles, if they exist.
        dd_enabled_interactions = (
            args.deep_data_enabled_interactions
            if args.deep_data_enabled_interactions
            else config_dict.get("deep_data_enabled_interactions", [])
        )

        _handle_baseline_profiles(args)

        _handle_profiles(args, dd_enabled_interactions)

        _handle_class_frequencies(args)

        LOGGER.debug("Moving contents to expected structure...")
        # Move each dex to a separate temporary directory to be operated by
        # redex.
        preserve_input_dexes = config_dict.get("preserve_input_dexes")
        dexen = relocate_dexen_to_directories(
            dex_dir,
            dex_glob(dex_dir),
            # pyrefly: ignore [bad-argument-type]
            preserve_input_dexes,
        )
        dexen_initial_state = DexenSnapshot(dex_dir) if preserve_input_dexes else None

        for store in sorted(store_files):
            dexen.append(store)

    if args.side_effect_summaries is not None:
        args.passthru_json.append(
            'ObjectSensitiveDcePass.side_effect_summaries="%s"'
            % args.side_effect_summaries
        )

    if args.escape_summaries is not None:
        args.passthru_json.append(
            'ObjectSensitiveDcePass.escape_summaries="%s"' % args.escape_summaries
        )

    for key_value_str in args.passthru_json:
        key_value = key_value_str.split("=", 1)
        if len(key_value) != 2:
            LOGGER.debug(
                "Json Pass through %s is not valid. Split len: %s",
                key_value_str,
                len(key_value),
            )
            continue
        key = key_value[0]
        value = key_value[1]
        prev_value = config_dict.get(key, "(No previous value)")
        LOGGER.debug(
            "Got Override %s = %s from %s. Previous %s",
            key,
            value,
            key_value_str,
            prev_value,
        )
        config_dict[key] = json.loads(value)

    # Scan for framework files. If not found, warn and add them if available.
    _check_android_sdk_api(args)
    # Check for shrinker heuristics.
    _check_shrinker_heuristics(args)

    # Scan for SDK jar provided. If not found, warn and add if available and allowed.
    _check_android_sdk_jar(args)

    LOGGER.debug("Running redex-all on %d dex files ", len(dexen))
    if args.lldb:
        debugger = "lldb"
    elif args.gdb:
        debugger = "gdb"
    else:
        debugger = None

    return State(
        args=args,
        config_dict=config_dict,
        debugger=debugger,
        dex_dir=dex_dir,
        dexen=dexen,
        extracted_apk_dir=extracted_apk_dir,
        stop_pass_idx=stop_pass_idx,
        lib_manager=lib_manager,
        unpack_manager=unpack_manager,
        zip_manager=zip_manager,
        dexen_initial_state=dexen_initial_state,
    )


def _is_preserve_input_dexes(args: argparse.Namespace) -> bool:
    if args.config is None:
        return False

    try:
        with open(args.config) as config_file:
            config_dict = json.load(config_file)

        return config_dict.get("preserve_input_dexes", False)
    except Exception as e:
        LOGGER.warning("Failed to read config file: %s", e)
    return False


def get_compression_list() -> typing.List[CompressionEntry]:
    return [
        CompressionEntry(
            "Redex Instrumentation Metadata",
            lambda args: args.enable_instrument_pass,
            True,
            ["redex-instrument-metadata.txt"],
            [
                "redex-source-block-method-dictionary.csv",
                "redex-source-blocks.csv",
                "redex-source-block-idom-maps.csv",
                "unique-idom-maps.txt",
            ],
            "redex-instrument-metadata.zip",
            "redex-instrument-checksum.txt",
            CompressionLevel.BETTER,  # Not as time-sensitive.
        ),
        CompressionEntry(
            "Redex Class Sizes",
            lambda args: True,
            True,
            [],
            ["redex-class-sizes.csv"],
            "redex-class-sizes.csv.zst",
            None,
            CompressionLevel.FAST,  # May be large.
        ),
        CompressionEntry(
            "Redex Class to Files Map",
            lambda args: True,
            True,
            [],
            ["redex-class-to-files-map.txt"],
            "redex-class-to-files-map.txt.zst",
            None,
            CompressionLevel.FAST,  # May be quite large.
        ),
        CompressionEntry(
            "Redex Stats",
            lambda args: True,
            False,
            ["redex-stats.txt"],
            [],
            None,
            None,
            CompressionLevel.BETTER,  # Usually small enough.
        ),
        CompressionEntry(
            "Redex Class Dependencies",
            lambda args: True,
            True,
            [],
            ["redex-class-dependencies.txt"],
            None,
            None,
            CompressionLevel.FAST,  # May be quite large.
        ),
        CompressionEntry(
            "Redex Unsafe Enums List",
            lambda args: True,
            True,
            [],
            ["redex-unsafe-enums.txt"],
            None,
            None,
            CompressionLevel.BETTER,  # Usually small enough.
        ),
        CompressionEntry(
            "Redex Unconditionally Throwing Classes",
            lambda args: True,
            True,
            [],
            ["redex-unconditionally-throwing-classes.txt"],
            None,
            None,
            CompressionLevel.BETTER,  # Usually small enough.
        ),
        CompressionEntry(
            "Redex Accessed Proguard Rules",
            lambda args: True,
            True,
            [],
            ["redex-used-proguard-rules.txt", "redex-unused-proguard-rules.txt"],
            "redex-accessed-proguard-rules.zip",
            None,
            CompressionLevel.BETTER,  # Usually small enough.
        ),
        CompressionEntry(
            "Redex InsertSourceBlocksPass Unresolved Methods",
            lambda args: True,
            True,
            [],
            ["redex-isb-unresolved-methods.txt"],
            None,
            None,
            CompressionLevel.BETTER,  # Usually small enough.
        ),
        CompressionEntry(
            "Redex InsertSourceBlocksPass Failed Methods",
            lambda args: True,
            True,
            [],
            ["redex-isb-failed-methods.txt"],
            None,
            None,
            CompressionLevel.BETTER,  # Usually small enough.
        ),
        CompressionEntry(
            "Redex Invoke Offset Map",
            lambda args: not _is_preserve_input_dexes(args),
            True,
            ["redex-invoke-map.jsonl"],
            [],
            "redex-invoke-map.jsonl.zst",
            None,
            CompressionLevel.DEFAULT,  # Bit larger.
        ),
        CompressionEntry(
            "Redex Full Rename Map",
            lambda args: not _is_preserve_input_dexes(args),
            False,
            ["redex-full-rename-map.txt"],
            [],
            "redex-full-rename-map.txt.zst",
            None,
            CompressionLevel.DEFAULT,  # Bit larger.
        ),
        CompressionEntry(
            "Redex Full Rename Map (JSON)",
            lambda args: not _is_preserve_input_dexes(args),
            True,
            ["redex-full-rename-map.jsonl"],
            [],
            "redex-full-rename-map.jsonl.zst",
            None,
            CompressionLevel.DEFAULT,  # Bit larger.
        ),
        CompressionEntry(
            "Redex Sparse Switches Data",
            lambda args: True,
            True,
            [],
            ["sparse_switches"],
            "redex-sparse-switches.tar.xz",
            None,
            CompressionLevel.DEFAULT,  # Bit larger.
        ),
        CompressionEntry(
            "Redex Class Rename Map",
            lambda args: not _is_preserve_input_dexes(args),
            False,
            ["redex-class-rename-map.txt"],
            [],
            "redex-class-rename-map.txt.zst",
            None,
            CompressionLevel.DEFAULT,  # Bit larger.
        ),
        CompressionEntry(
            "Redex Method ID Map",
            lambda args: not _is_preserve_input_dexes(args),
            False,
            # Not written in no-custom-debug mode, too complicated to filter.
            [],
            ["redex-method-id-map.txt"],
            "redex-method-id-map.txt.zst",
            None,
            # Large. BETTER would raise the window to 128MB, and with it the
            # multi-threading job size to 512MB, so the whole map compresses as
            # a single job: ~40s instead of ~0.5s, for ~20% off.
            CompressionLevel.DEFAULT,
        ),
        CompressionEntry(
            "Redex Resource Mapping",
            lambda args: not _is_preserve_input_dexes(args),
            False,
            # Only written when resource files are renamed.
            [],
            ["resource-mapping.txt"],
            "redex-resource-mapping.txt.zst",
            None,
            CompressionLevel.BETTER,
        ),
        CompressionEntry(
            "Redex Class ID Map",
            lambda args: not _is_preserve_input_dexes(args),
            False,
            # Not written in no-custom-debug mode, too complicated to filter.
            [],
            ["redex-class-id-map.txt"],
            "redex-class-id-map.txt.zst",
            None,
            CompressionLevel.BETTER,  # Usually small.
        ),
        CompressionEntry(
            "Redex Line Number Map",
            lambda args: not _is_preserve_input_dexes(args),
            # Many services still expect the uncompressed file.
            False,
            # Not written in no-custom-symbolication mode, too complicated to filter.
            [],
            ["redex-line-number-map-v2"],
            "redex-line-number-map-v2.zst",
            None,
            CompressionLevel.FAST,  # Large, and not much difference to default size.
        ),
        CompressionEntry(
            "Redex Debug Line Map",
            lambda args: not _is_preserve_input_dexes(args),
            # Many services still expect the uncompressed file.
            False,
            # Only written when addresses are needed, i.e. no-positions or IODI.
            [],
            ["redex-debug-line-map-v2"],
            "redex-debug-line-map-v2.zst",
            None,
            CompressionLevel.FAST,  # Large, and not much difference to default size.
        ),
        CompressionEntry(
            "Redex ISB SB To Line Map",
            lambda args: True,
            True,
            [],
            ["redex-isb-sb-to-lines-mapping.jsonl"],
            "redex-isb-sb-to-lines-mapping.jsonl.zst",
            None,
            CompressionLevel.FAST,  # Large, and not much difference to default size.
        ),
        CompressionEntry(
            "Redex Reachability Graph",
            lambda args: True,
            False,
            [],
            ["reachability-graph"],
            "redex-reachability-graph.zst",
            None,
            CompressionLevel.FAST,  # Large.
        ),
        CompressionEntry(
            "Redex Method Override Graph",
            lambda args: True,
            False,
            [],
            ["method-override-graph"],
            "redex-method-override-graph.zst",
            None,
            CompressionLevel.FAST,  # Large.
        ),
        CompressionEntry(
            "Redex Removed Reachability Graph",
            lambda args: True,
            True,
            [],
            ["redex-removed-reachability-graph"],
            "redex-removed-reachability-graph.zst",
            None,
            CompressionLevel.FAST,  # Large.
        ),
    ]


def finalize_redex(state: State) -> None:
    if state.args.verify_dexes:
        verify_dexes(state.dex_dir, state.args.verify_dexes)

    if state.dexen_initial_state is not None:
        dexen_final_state = DexenSnapshot(state.dex_dir)
        assert _assert_val(state.dexen_initial_state).equals(
            dexen_final_state
        ), "initial state of preserved dex files does not match final state"

    _assert_val(state.lib_manager).__exit__(*sys.exc_info())

    with timed_scope("Creating output APK"):
        with timed_scope("Undoing unpack"):
            _assert_val(state.unpack_manager).__exit__(*sys.exc_info())

        meta_file_dir = join(state.dex_dir, "meta/")
        assert os.path.isdir(meta_file_dir), (
            "meta dir %s does not exist" % meta_file_dir
        )

        with timed_scope("Rezipping"):
            resource_file_mapping = join(meta_file_dir, "resource-mapping.txt")
            if os.path.exists(resource_file_mapping):
                _assert_val(state.zip_manager).set_resource_file_mapping(
                    resource_file_mapping
                )
            _assert_val(state.zip_manager).__exit__(*sys.exc_info())

        with timed_scope("Aligning and signing"):
            page_align = PageAlignment.from_args(
                state.args.page_align_libs,
                state.args.page_align_libs_16kb,
            )
            align_and_sign_output_apk(
                _assert_val(state.zip_manager).output_apk,
                state.args.out,
                # In dev mode, reset timestamps.
                state.args.reset_zip_timestamps or state.args.dev,
                state.args.sign,
                state.args.sign_v4,
                extract_signing_args(state.args, fail_on_error=False),
                state.args.ignore_zipalign,
                state.args.ignore_apksigner,
                page_align,
            )

    with timed_scope("Arranging output dir"):
        compress_entries(
            get_compression_list(),
            meta_file_dir,
            os.path.dirname(state.args.out),
            state.args,
        )

        copy_all_file_to_out_dir(
            meta_file_dir, state.args.out, "*", "all redex generated artifacts"
        )

        redex_stats_filename = state.config_dict.get("stats_output", "redex-stats.txt")
        redex_stats_file = join(dirname(meta_file_dir), redex_stats_filename)
        if isfile(redex_stats_file):
            with open(redex_stats_file, "r") as fr:
                apk_input_size = getsize(state.args.input_apk)
                apk_output_size = getsize(state.args.out)
                redex_stats_json = json.load(fr)
                redex_stats_json["input_stats"]["total_stats"][
                    "num_compressed_apk_bytes"
                ] = apk_input_size
                redex_stats_json["output_stats"]["total_stats"][
                    "num_compressed_apk_bytes"
                ] = apk_output_size
                update_redex_stats_file = join(
                    dirname(state.args.out), redex_stats_filename
                )
                with open(update_redex_stats_file, "w") as fw:
                    json.dump(redex_stats_json, fw)

        # Write invocation file
        with open(join(dirname(state.args.out), "redex.py-invocation.txt"), "w") as f:
            print("%s" % " ".join(map(shlex.quote, sys.argv)), file=f)

        copy_all_file_to_out_dir(
            state.dex_dir, state.args.out, "*.dot", "approximate shape graphs"
        )

    # Write stored logs, if any.
    logger.copy_store_logs_to(join(dirname(state.args.out), "redex-log.txt.xz"))


def _init_logging(level_str: str) -> None:
    levels = {
        "critical": logging.CRITICAL,
        "error": logging.ERROR,
        "warn": logging.WARNING,
        "warning": logging.WARNING,
        "info": logging.INFO,
        "debug": logging.DEBUG,
    }
    level = levels[level_str]
    logging.basicConfig(
        level=level,
        format="[%(levelname)-8s][%(asctime)-23s][%(name)-16s] %(message)s",
    )


def run_redex_passthrough(
    args: argparse.Namespace,
    exception_formatter: ExceptionMessageFormatter,
    output_line_handler: typing.Optional[typing.Callable[[str], str]],
) -> None:
    assert args.outdir
    assert args.dex_files

    if args.addr2line:
        bintools.set_addr2line_path(args.addr2line)

    state = State(
        args=args,
        config_dict={},
        debugger=None,
        dex_dir=args.outdir,
        dexen=[],
        extracted_apk_dir=None,
        stop_pass_idx=-1,
        lib_manager=None,
        unpack_manager=None,
        zip_manager=None,
        dexen_initial_state=None,
    )
    run_redex_binary(state, exception_formatter, output_line_handler)


def run_redex(
    args: argparse.Namespace,
    exception_formatter: typing.Optional[ExceptionMessageFormatter] = None,
    output_line_handler: typing.Optional[typing.Callable[[str], str]] = None,
) -> None:
    if exception_formatter is None:
        exception_formatter = ExceptionMessageFormatter()

    if args.outdir or args.dex_files:
        run_redex_passthrough(args, exception_formatter, output_line_handler)
        return
    else:
        assert args.input_apk

    with timed_scope("Prepare to run redex"):
        state = prepare_redex(args)

    with timed_scope("Actually run redex binary"):
        run_redex_binary(state, exception_formatter, output_line_handler)

    if args.stop_pass:
        # Do not remove temp dirs
        sys.exit()

    finalize_redex(state)


def early_apply_args(args: argparse.Namespace) -> None:
    # This is late, but hopefully early enough.
    _init_logging(args.log_level)
    if args.store_logs:
        logger.setup_store_logs_temp_file()

    # Translate these to the regular environment variables.
    if args.trace:
        os.environ["TRACE"] = args.trace

    if args.trace_file:
        os.environ["TRACEFILE"] = args.trace_file
    if args.after_pass_trace_file:
        os.environ["TRACE_CLASS_FILE"] = args.after_pass_trace_file
    if args.trace_class_name:
        os.environ["TRACE_CLASS_NAME"] = args.trace_class_name
    if args.trace_method_name:
        os.environ["TRACE_METHOD_NAME"] = args.trace_method_name


if __name__ == "__main__":
    args: argparse.Namespace = arg_parser().parse_args()
    early_apply_args(args)
    validate_args(args)
    with_temp_cleanup(lambda: run_redex(args), args.always_clean_up)
