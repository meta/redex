#!/usr/bin/env python3
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.


# pyre-strict


import fnmatch
import hashlib
import itertools
import json
import logging
import lzma
import mmap
import os
import platform
import re
import shutil
import subprocess
import tarfile
import typing
import zipfile
from abc import ABC, abstractmethod
from collections import defaultdict
from os.path import basename, dirname, getsize, isdir, isfile, join, normpath

from pyredex.logger import log
from pyredex.utils import (
    abs_glob,
    ensure_libs_dir,
    get_xz_path,
    make_temp_dir,
    module_dex_glob,
    remove_signature_files,
)


LOGGER: logging.Logger = logging.getLogger(__name__)


class BaseDexMode(ABC):
    def __init__(
        self,
        primary_dir: str,
        dex_prefix: str,
        canary_prefix: typing.Optional[str],
        store_id: typing.Optional[str],
        dependencies: typing.Optional[typing.List[str]],
    ) -> None:
        self._primary_dir = primary_dir
        self._dex_prefix = dex_prefix
        self._canary_prefix = canary_prefix
        self._store_id = store_id
        self._dependencies = dependencies

    @abstractmethod
    def detect(self, extracted_apk_dir: str) -> bool:
        return False

    @abstractmethod
    def unpackage(self, extracted_apk_dir: str, dex_dir: str) -> None:
        primary_dex = join(
            extracted_apk_dir, self._primary_dir, self._dex_prefix + ".dex"
        )
        if os.path.exists(primary_dex):
            shutil.move(primary_dex, dex_dir)

    @abstractmethod
    def repackage(
        self,
        extracted_apk_dir: str,
        dex_dir: str,
        have_locators: bool,
        locator_store_id: int,
        fast_repackage: bool,
        reset_timestamps: bool,
    ) -> None:
        primary_dex = join(dex_dir, self._dex_prefix + ".dex")
        if os.path.exists(primary_dex):
            shutil.move(primary_dex, join(extracted_apk_dir, self._primary_dir))

    def get_canary(self, i: int) -> str:
        canary_prefix = self._canary_prefix
        assert canary_prefix is not None
        return canary_prefix + ".dex%02d.Canary" % i


class ApplicationModule(object):
    def __init__(
        self,
        extracted_apk_dir: str,
        name: str,
        canary_prefix: typing.Optional[str],
        dependencies: typing.List[str],
        split: str = "",
    ) -> None:
        self.name = name
        self.path: str = join(split, "assets", name)
        self.split_dex_path: str = join(split, "dex") if split else ""
        self.canary_prefix = canary_prefix
        self.dependencies = dependencies
        self.dex_mode: typing.Optional[BaseDexMode] = None

    @staticmethod
    def detect(
        extracted_apk_dir: str, is_bundle: bool = False
    ) -> typing.List["ApplicationModule"]:
        modules = []
        pattern = "*/assets/*/metadata.txt" if is_bundle else "assets/*/metadata.txt"
        for candidate in abs_glob(extracted_apk_dir, pattern):
            with open(candidate) as metadata:
                name = None
                dependencies: typing.List[str] = []
                canary_match = None
                canary_prefix = None
                for line in metadata.read().splitlines():
                    tokens = line.split()
                    if tokens[0] == ".id":
                        name = tokens[1]
                    if tokens[0] == ".requires":
                        dependencies.append(tokens[1])
                    if tokens[0][0] != ".":
                        canary_match = re.search(
                            "([A-Za-z0-9]*)[.]dex[0-9][0-9_]*[.]Canary", tokens[2]
                        )
                        if canary_match is not None:
                            canary_prefix = canary_match.group(1)
                if name is not None:
                    split = (
                        basename(normpath(join(candidate, "../../../")))
                        if is_bundle
                        else ""
                    )
                    modules.append(
                        ApplicationModule(
                            extracted_apk_dir, name, canary_prefix, dependencies, split
                        )
                    )
        modules.sort(key=lambda m: m.path)
        return modules

    def get_name(self) -> str:
        return self.name

    def get_canary_prefix(self) -> typing.Optional[str]:
        return self.canary_prefix

    def write_redex_metadata(self, path: str, metadata_file: str) -> None:
        metadata = {
            "id": self.name,
            "requires": self.dependencies,
            "files": module_dex_glob(path, self.name),
        }
        with open(metadata_file, "w") as store_metadata:
            json.dump(metadata, store_metadata)

    def unpackage(
        self, extracted_apk_dir: str, dex_dir: str, unpackage_metadata: bool = False
    ) -> None:
        dex_mode = XZSDexMode(
            secondary_dir=self.path,
            store_name=self.name,
            dex_prefix=self.name,
            canary_prefix=self.canary_prefix,
            store_id=self.name,
            dependencies=self.dependencies,
        )
        if dex_mode.detect(extracted_apk_dir):
            self.dex_mode = dex_mode
            log("module " + self.name + " is XZSDexMode")
            dex_mode.unpackage(extracted_apk_dir, dex_dir, unpackage_metadata)
            return

        dex_mode = SubdirDexMode(
            secondary_dir=self.path,
            store_name=self.name,
            dex_prefix=self.name,
            canary_prefix=self.canary_prefix,
            store_id=self.name,
            dependencies=self.dependencies,
        )
        if dex_mode.detect(extracted_apk_dir):
            self.dex_mode = dex_mode
            log("module " + self.name + " is SubdirDexMode")
            dex_mode.unpackage(extracted_apk_dir, dex_dir, unpackage_metadata)
            return

        dex_mode = RawSubdirDexMode(
            secondary_dir=self.path,
            store_name=self.name,
            dex_prefix=self.name,
            canary_prefix=self.canary_prefix,
            store_id=self.name,
            dependencies=self.dependencies,
        )
        if dex_mode.detect(extracted_apk_dir):
            self.dex_mode = dex_mode
            log("module " + self.name + " is RawSubdirDexMode")
            dex_mode.unpackage(extracted_apk_dir, dex_dir, unpackage_metadata)
            return

        # Special case for aab inputs, for which we put .dex files into modulename/dex
        # and our metadata file in a separate location modulename/assets/modulename.
        if self.split_dex_path:
            dex_mode = Api21NativeModuleDexMode(
                secondary_dir=self.split_dex_path,
                store_name=self.name,
                canary_prefix=self.canary_prefix,
                store_id=self.name,
                dependencies=self.dependencies,
                metadata_dir=self.path,
            )
            if dex_mode.detect(extracted_apk_dir):
                self.dex_mode = dex_mode
                log("module " + self.name + " is aab Api21NativeModuleDexMode")
                dex_mode.unpackage(extracted_apk_dir, dex_dir, unpackage_metadata)
                return

        dex_mode = Api21NativeModuleDexMode(
            secondary_dir=self.path,
            store_name=self.name,
            canary_prefix=self.canary_prefix,
            store_id=self.name,
            dependencies=self.dependencies,
        )
        if dex_mode.detect(extracted_apk_dir):
            self.dex_mode = dex_mode
            log("module " + self.name + " is Api21NativeModuleDexMode")
            dex_mode.unpackage(extracted_apk_dir, dex_dir, unpackage_metadata)
            return

        dex_mode = Api21ModuleDexMode(
            secondary_dir=self.path,
            store_name=self.name,
            canary_prefix=self.canary_prefix,
            store_id=self.name,
            dependencies=self.dependencies,
        )
        self.dex_mode = dex_mode
        log("module " + self.name + " is Api21ModuleDexMode")
        dex_mode.unpackage(extracted_apk_dir, dex_dir, unpackage_metadata)

    def repackage(
        self,
        extracted_apk_dir: str,
        dex_dir: str,
        have_locators: bool,
        locator_store_id: int,
        fast_repackage: bool,
        reset_timestamps: bool,
    ) -> None:
        dex_mode = self.dex_mode
        assert dex_mode is not None
        dex_mode.repackage(
            extracted_apk_dir,
            dex_dir,
            have_locators,
            locator_store_id,
            fast_repackage,
            reset_timestamps,
        )


class DexMetadata(object):
    def __init__(
        self,
        store: typing.Optional[str] = None,
        dependencies: typing.Optional[typing.List[str]] = None,
        have_locators: bool = False,
        is_root_relative: bool = False,
        locator_store_id: int = 0,
        superpack_files: int = 0,
    ) -> None:
        self._have_locators = False
        self._store = store
        self._dependencies = dependencies
        self._have_locators = have_locators
        self._is_root_relative = is_root_relative
        self._dexen: typing.List[typing.Tuple[str, str, str]] = []
        self._locator_store_id = locator_store_id
        self.superpack_files = superpack_files

    def add_dex(
        self, dex_path: str, canary_class: str, hash: typing.Optional[str] = None
    ) -> None:
        if hash is None:
            with open(dex_path, "rb") as dex:
                sha1hash = hashlib.sha1(dex.read()).hexdigest()
        else:
            sha1hash = hash
        self._dexen.append((os.path.basename(dex_path), sha1hash, canary_class))

    def write(self, path: str) -> None:
        with open(path, "w") as meta:
            store = self._store
            if store is not None:
                meta.write(".id " + store + "\n")
            deps = self._dependencies
            if deps is not None:
                for dependency in deps:
                    meta.write(".requires " + dependency + "\n")
            if self._is_root_relative:
                meta.write(".root_relative\n")
            if self._have_locators:
                meta.write(".locators\n")
            if self._locator_store_id > 0:
                meta.write(".locator_id " + str(self._locator_store_id) + "\n")
            if self.superpack_files > 0:
                meta.write(".superpack_files " + str(self.superpack_files) + "\n")
            for dex in self._dexen:
                meta.write(" ".join(dex) + "\n")

    def dex_len(self) -> int:
        return len(self._dexen)


class Api21DexMode(BaseDexMode):
    """
    On API 21+, secondary dex files are in the root of the apk and are named
    classesN.dex for N in [2, 3, 4, ... ]

    Note that this mode will also be used for apps that don't have any
    secondary dex files.
    """

    def __init__(
        self,
        primary_dir: str = "",
        secondary_dir: str = "assets/secondary-program-dex-jars",
        dex_prefix: str = "classes",
        canary_prefix: typing.Optional[str] = "secondary",
        is_root_relative: bool = True,
        store_id: typing.Optional[str] = None,
        dependencies: typing.Optional[typing.List[str]] = None,
    ) -> None:
        BaseDexMode.__init__(
            self, primary_dir, dex_prefix, canary_prefix, store_id, dependencies
        )
        self._secondary_dir = secondary_dir
        self._is_root_relative = is_root_relative

    def detect(self, extracted_apk_dir: str) -> bool:
        # Note: This mode is the fallback and we only check for it after
        # checking for the other modes. This should return true for any
        # apk.
        return isfile(
            join(extracted_apk_dir, self._primary_dir, self._dex_prefix + ".dex")
        )

    def unpackage(
        self, extracted_apk_dir: str, dex_dir: str, unpackage_metadata: bool = False
    ) -> None:
        BaseDexMode.unpackage(self, extracted_apk_dir, dex_dir)

        metadata_dir = join(extracted_apk_dir, self._secondary_dir)
        if self._is_root_relative:
            extracted_dex_dir = join(extracted_apk_dir, self._primary_dir)
        else:
            extracted_dex_dir = metadata_dir
        for path in abs_glob(extracted_dex_dir, "*.dex"):
            shutil.move(path, dex_dir)

    def repackage(
        self,
        extracted_apk_dir: str,
        dex_dir: str,
        have_locators: bool,
        locator_store_id: int = 0,
        fast_repackage: bool = False,
        reset_timestamps: bool = True,
    ) -> None:
        BaseDexMode.repackage(
            self,
            extracted_apk_dir,
            dex_dir,
            have_locators,
            locator_store_id,
            fast_repackage,
            reset_timestamps,
        )
        metadata_dir = join(extracted_apk_dir, self._secondary_dir)

        metadata = DexMetadata(
            is_root_relative=self._is_root_relative,
            have_locators=have_locators,
            store=self._store_id,
            dependencies=self._dependencies,
            locator_store_id=locator_store_id,
        )
        for i in itertools.count(2):
            dex_path = join(dex_dir, self._dex_prefix + "%d.dex" % i)
            if not isfile(dex_path):
                break
            metadata.add_dex(dex_path, BaseDexMode.get_canary(self, i - 1))
            if self._is_root_relative:
                shutil.move(dex_path, join(extracted_apk_dir, self._primary_dir))
            else:
                shutil.move(dex_path, metadata_dir)
        if os.path.exists(metadata_dir):
            metadata.write(join(metadata_dir, "metadata.txt"))


class Api21ModuleDexMode(Api21DexMode):
    """
    modules built in Api21 builds will just have <store_name><i>.dex files in
    the module directory.  This should only be used by modules.
    """

    def __init__(
        self,
        secondary_dir: str,
        store_name: str = "secondary",
        canary_prefix: typing.Optional[str] = "secondary",
        store_id: typing.Optional[str] = None,
        dependencies: typing.Optional[typing.List[str]] = None,
    ) -> None:
        Api21DexMode.__init__(
            self,
            primary_dir="",
            secondary_dir=secondary_dir,
            dex_prefix=store_name,
            canary_prefix=canary_prefix,
            store_id=store_id,
            dependencies=dependencies,
            is_root_relative=False,
        )
        self._store_name = store_name

    def detect(self, extracted_apk_dir: str) -> bool:
        secondary_dex_dir = join(extracted_apk_dir, self._secondary_dir)
        return len(list(abs_glob(secondary_dex_dir, "*.dex"))) > 0


class Api21NativeModuleDexMode(Api21DexMode):
    """
    modules built in this mode will just have classes.dex, classes2.dex, etc
    files in the module directory.  This should only be used by modules.
    """

    def __init__(
        self,
        secondary_dir: str,
        store_name: str = "secondary",
        canary_prefix: typing.Optional[str] = "secondary",
        store_id: typing.Optional[str] = None,
        dependencies: typing.Optional[typing.List[str]] = None,
        metadata_dir: typing.Optional[str] = None,
    ) -> None:
        Api21DexMode.__init__(
            self,
            primary_dir=secondary_dir,  # intentional that this is the same as secondary dir; everything is in the same dir
            secondary_dir=secondary_dir,
            canary_prefix=canary_prefix,
            store_id=store_id,
            dependencies=dependencies,
            is_root_relative=False,
        )
        self._store_name = store_name
        self._metadata_dir: str = secondary_dir if not metadata_dir else metadata_dir

    def detect(self, extracted_apk_dir: str) -> bool:
        secondary_dex_dir = join(extracted_apk_dir, self._secondary_dir)
        return len(list(abs_glob(secondary_dex_dir, "classes.*dex"))) > 0

    def repackage(
        self,
        extracted_apk_dir: str,
        dex_dir: str,
        have_locators: bool,
        locator_store_id: int = 0,
        fast_repackage: bool = False,
        reset_timestamps: bool = True,
    ) -> None:
        metadata = DexMetadata(
            is_root_relative=self._is_root_relative,
            have_locators=have_locators,
            store=self._store_id,
            dependencies=self._dependencies,
            locator_store_id=locator_store_id,
        )
        # pick up the janky naming convention used by C++ layer which is going name via <store_name><i>.dex
        for i in itertools.count(2):
            dex_path = join(dex_dir, self._store_name + "%d.dex" % i)
            if not isfile(dex_path):
                break
            len = metadata.dex_len()
            dest = join(
                extracted_apk_dir,
                self._primary_dir,
                "classes.dex" if len == 0 else "classes%d.dex" % (len + 1),
            )
            shutil.move(dex_path, dest)
            metadata.add_dex(dest, BaseDexMode.get_canary(self, i - 1))

        metadata_dir = join(extracted_apk_dir, self._metadata_dir)
        if os.path.exists(metadata_dir):
            metadata.write(join(metadata_dir, "metadata.txt"))


class SubdirDexMode(BaseDexMode):
    """
    `buck build katana` places secondary dexes in a subdir with no compression
    """

    def __init__(
        self,
        primary_dir: str = "",
        secondary_dir: str = "assets/secondary-program-dex-jars",
        store_name: str = "secondary",
        dex_prefix: str = "classes",
        canary_prefix: typing.Optional[str] = "secondary",
        store_id: typing.Optional[str] = None,
        dependencies: typing.Optional[typing.List[str]] = None,
    ) -> None:
        BaseDexMode.__init__(
            self, primary_dir, dex_prefix, canary_prefix, store_id, dependencies
        )
        self._secondary_dir = secondary_dir
        self._store_name = store_name

    def detect(self, extracted_apk_dir: str) -> bool:
        secondary_dex_dir = join(extracted_apk_dir, self._secondary_dir)
        # pyre-fixme[7]: Expected `bool` but got `int`.
        return isdir(secondary_dex_dir) and len(
            list(abs_glob(secondary_dex_dir, "*.dex.jar"))
        )

    def unpackage(
        self, extracted_apk_dir: str, dex_dir: str, unpackage_metadata: bool = False
    ) -> None:
        jars = abs_glob(join(extracted_apk_dir, self._secondary_dir), "*.dex.jar")
        for jar in jars:
            dexpath = join(dex_dir, basename(jar))[:-4]
            extract_dex_from_jar(jar, dexpath)
            os.remove(jar + ".meta")
            os.remove(jar)
        metadata_txt = join(extracted_apk_dir, self._secondary_dir, "metadata.txt")
        if unpackage_metadata:
            shutil.copy(metadata_txt, dex_dir)
        os.remove(metadata_txt)
        BaseDexMode.unpackage(self, extracted_apk_dir, dex_dir)

    def repackage(
        self,
        extracted_apk_dir: str,
        dex_dir: str,
        have_locators: bool,
        locator_store_id: int = 0,
        fast_repackage: bool = False,
        reset_timestamps: bool = True,
    ) -> None:
        BaseDexMode.repackage(
            self,
            extracted_apk_dir,
            dex_dir,
            have_locators,
            locator_store_id,
            fast_repackage,
            reset_timestamps,
        )

        metadata = DexMetadata(
            have_locators=have_locators,
            store=self._store_id,
            dependencies=self._dependencies,
            locator_store_id=locator_store_id,
        )
        for i in itertools.count(1):
            oldpath = join(dex_dir, self._dex_prefix + "%d.dex" % (i + 1))
            dexpath = join(dex_dir, self._store_name + "-%d.dex" % i)
            if not isfile(oldpath):
                break
            shutil.move(oldpath, dexpath)

            jarpath = dexpath + ".jar"
            create_dex_jar(jarpath, dexpath, reset_timestamps=reset_timestamps)
            metadata.add_dex(jarpath, BaseDexMode.get_canary(self, i))

            dex_meta_base = jarpath + ".meta"
            dex_meta_path = join(dex_dir, dex_meta_base)
            with open(dex_meta_path, "w") as dex_meta:
                dex_meta.write("jar:%d dex:%d\n" % (getsize(jarpath), getsize(dexpath)))

            shutil.move(dex_meta_path, join(extracted_apk_dir, self._secondary_dir))
            shutil.move(jarpath, join(extracted_apk_dir, self._secondary_dir))
        jar_meta_path = join(dex_dir, "metadata.txt")
        metadata.write(jar_meta_path)
        shutil.move(jar_meta_path, join(extracted_apk_dir, self._secondary_dir))


class RawSubdirDexMode(SubdirDexMode):
    def __init__(
        self,
        primary_dir: str = "",
        secondary_dir: str = "assets/secondary-program-dex-jars",
        store_name: str = "secondary",
        dex_prefix: str = "classes",
        canary_prefix: typing.Optional[str] = "secondary",
        store_id: typing.Optional[str] = None,
        dependencies: typing.Optional[typing.List[str]] = None,
    ) -> None:
        SubdirDexMode.__init__(
            self,
            primary_dir,
            secondary_dir,
            store_name,
            dex_prefix,
            canary_prefix,
            store_id,
            dependencies,
        )

    def detect(self, extracted_apk_dir: str) -> bool:
        secondary_dex_dir = join(extracted_apk_dir, self._secondary_dir)
        return isdir(secondary_dex_dir) and any(
            abs_glob(secondary_dex_dir, "secondary-*.dex")
        )

    def unpackage(
        self, extracted_apk_dir: str, dex_dir: str, unpackage_metadata: bool = False
    ) -> None:
        raw_dexes = abs_glob(
            join(extracted_apk_dir, self._secondary_dir), "secondary-*.dex"
        )
        for raw_dex in raw_dexes:
            shutil.move(raw_dex, dex_dir)

        metadata_txt = join(extracted_apk_dir, self._secondary_dir, "metadata.txt")
        if unpackage_metadata:
            shutil.copy(metadata_txt, dex_dir)
        os.remove(metadata_txt)
        BaseDexMode.unpackage(self, extracted_apk_dir, dex_dir)

    def repackage(
        self,
        extracted_apk_dir: str,
        dex_dir: str,
        have_locators: bool,
        locator_store_id: int = 0,
        fast_repackage: bool = False,
        reset_timestamps: bool = True,
    ) -> None:
        BaseDexMode.repackage(
            self,
            extracted_apk_dir,
            dex_dir,
            have_locators,
            locator_store_id,
            fast_repackage,
            reset_timestamps,
        )

        metadata = DexMetadata(
            have_locators=have_locators,
            store=self._store_id,
            dependencies=self._dependencies,
            locator_store_id=locator_store_id,
        )

        # Check which prefix we have for dex files.
        has_class_prefix_dex = any(abs_glob(dex_dir, f"{self._dex_prefix}?*.dex"))
        has_secondary_prefix_dex = any(abs_glob(dex_dir, "secondary-?*.dex"))
        assert not (
            has_class_prefix_dex and has_secondary_prefix_dex
        ), "should not have dex files with mixed prefixes"

        for i in itertools.count(1):
            dex_file = self._store_name + f"-{i}.dex"
            dexpath = join(dex_dir, dex_file)

            if has_class_prefix_dex:
                oldpath = join(dex_dir, self._dex_prefix + "%d.dex" % (i + 1))
                if isfile(oldpath):
                    shutil.move(oldpath, join(dex_dir, f"secondary-{i}.dex"))

            # if store_name is not "secondary" (the default),
            # we need to rename the dex files
            if self._store_name != "secondary":
                # The n in "secondary-n.dex" always starts at 1
                oldpath = join(dex_dir, f"secondary-{i}.dex")
                if isfile(oldpath):
                    shutil.move(oldpath, dexpath)

            if not isfile(dexpath):
                break

            metadata.add_dex(dexpath, BaseDexMode.get_canary(self, i))
            shutil.move(dexpath, join(extracted_apk_dir, self._secondary_dir))

        dex_meta_path = join(dex_dir, "metadata.txt")
        metadata.write(dex_meta_path)
        shutil.move(dex_meta_path, join(extracted_apk_dir, self._secondary_dir))


warned_about_xz = False


def _warn_xz() -> None:
    global warned_about_xz
    if not warned_about_xz:
        LOGGER.warning(
            "Falling back to python lzma. For increased performance, install xz."
        )
        warned_about_xz = True


def unpack_xz(input: str, output: str) -> None:
    xz = get_xz_path()
    if xz is not None:
        with open(input, "rb") as fin:
            with open(output, "wb") as fout:
                cmd = [xz, "-d", "--threads", "6"]
                subprocess.check_call(cmd, stdin=fin, stdout=fout)
                return

    _warn_xz()

    with lzma.open(input, "rb") as input_f:
        with open(output, "wb") as output_f:
            BUF_SIZE = 4 * 1024 * 1024
            while True:
                buf = input_f.read(BUF_SIZE)
                if not buf:
                    break
                output_f.write(buf)


def pack_xz(
    input: str,
    output: str,
    compression_level: typing.Union[int, str] = 9,
    threads: int = 6,
    check: int = lzma.CHECK_CRC32,
) -> None:
    # See whether the `xz` binary exists. It may be faster because of multithreaded encoding.
    xz = get_xz_path()
    if xz is not None:
        check_map = {
            lzma.CHECK_CRC32: "crc32",
            lzma.CHECK_CRC64: "crc64",
            lzma.CHECK_SHA256: "sha256",
            lzma.CHECK_NONE: None,
            None: None,
        }
        check_str = check_map[check]
        with open(input, "rb") as fin:
            with open(output, "wb") as fout:
                cmd = [
                    xz,
                    f"-z{compression_level}",
                    f"--threads={threads}",
                    "-c",
                    f"--check={check_str}" if check_str else "",
                ]
                subprocess.check_call(
                    cmd,
                    stdin=fin,
                    stdout=fout,
                )
                return

    _warn_xz()
    assert isinstance(compression_level, int)

    c = lzma.LZMACompressor(
        format=lzma.FORMAT_XZ, check=check, preset=compression_level
    )
    with open(output, "wb") as output_f:
        with open(input, "rb") as input_f:
            BUF_SIZE = 4 * 1024 * 1024
            while True:
                buf = input_f.read(BUF_SIZE)
                if not buf:
                    break
                c_buf = c.compress(buf)
                output_f.write(c_buf)
        end_buf = c.flush()
        output_f.write(end_buf)


def unpack_tar_xz(input: str, output_dir: str) -> None:
    # See whether the `xz` binary exists. It may be faster because of multithreaded decoding.
    if shutil.which("tar"):
        xz = get_xz_path()

        if xz is not None:
            if platform.system() != "Darwin":
                additional_arg = f"--use-compress-program={xz}"
            else:
                additional_arg = f"--use-compress-program={xz} -d"
            cmd = [
                "tar",
                "xf",
                input,
                "-C",
                output_dir,
                additional_arg,
            ]
            subprocess.check_call(cmd)
            return

    _warn_xz()

    with tarfile.open(name=input, mode="r:xz") as t:
        os.makedirs(output_dir, exist_ok=True)
        def is_within_directory(directory, target):
            
            abs_directory = os.path.abspath(directory)
            abs_target = os.path.abspath(target)
        
            prefix = os.path.commonprefix([abs_directory, abs_target])
            
            return prefix == abs_directory
        
        def safe_extract(tar, path=".", members=None, *, numeric_owner=False):
        
            for member in tar.getmembers():
                member_path = os.path.join(path, member.name)
                if not is_within_directory(path, member_path):
                    raise Exception("Attempted Path Traversal in Tar File")
        
            tar.extractall(path, members, numeric_owner=numeric_owner) 
            
        
        safe_extract(t, output_dir)


class XZSDexMode(BaseDexMode):
    """
    Secondary dex files are packaged in individual jar files where are then
    concatenated together and compressed with xz.

    ... This format is completely insane.
    """

    def __init__(
        self,
        primary_dir: str = "",
        secondary_dir: str = "assets/secondary-program-dex-jars",
        store_name: str = "secondary",
        dex_prefix: str = "classes",
        canary_prefix: typing.Optional[str] = "secondary",
        store_id: typing.Optional[str] = None,
        dependencies: typing.Optional[typing.List[str]] = None,
    ) -> None:
        BaseDexMode.__init__(
            self, primary_dir, dex_prefix, canary_prefix, store_id, dependencies
        )
        self._xzs_dir = secondary_dir
        self._xzs_filename: str = store_name + ".dex.jar.xzs"
        self._store_name = store_name

    def detect(self, extracted_apk_dir: str) -> bool:
        path = join(extracted_apk_dir, self._xzs_dir, self._xzs_filename)
        return isfile(path)

    def unpackage(
        self, extracted_apk_dir: str, dex_dir: str, unpackage_metadata: bool = False
    ) -> None:
        src = join(extracted_apk_dir, self._xzs_dir, self._xzs_filename)
        dest = join(dex_dir, self._xzs_filename)

        # Move secondary dexen
        shutil.move(src, dest)

        # concat_jar is a bunch of .dex.jar files concatenated together.
        concat_jar = join(dex_dir, self._xzs_filename[:-4])
        unpack_xz(dest, concat_jar)

        if unpackage_metadata:
            shutil.copy(join(extracted_apk_dir, self._xzs_dir, "metadata.txt"), dex_dir)

        dex_order = []
        with open(
            join(extracted_apk_dir, self._xzs_dir, "metadata.txt")
        ) as dex_metadata:
            for line in dex_metadata.read().splitlines():
                if line[0] != ".":
                    tokens = line.split()
                    search_pattern = self._store_name + r"-(\d+)\.dex\.jar\.xzs\.tmp~"
                    match = re.search(search_pattern, tokens[0])
                    if match is None:
                        raise Exception(
                            "unable to find match in "
                            + tokens[0]
                            + " for "
                            + search_pattern
                        )
                    dex_order.append(int(match.group(1)))

        # Sizes of the concatenated .dex.jar files are stored in .meta files.
        # Read the sizes of each .dex.jar file and un-concatenate them.
        jar_size_regex = r"jar:(\d+)"
        secondary_dir = join(extracted_apk_dir, self._xzs_dir)
        jar_sizes = {}
        for i in dex_order:
            filename = self._store_name + "-%d.dex.jar.xzs.tmp~.meta" % i
            metadata_path = join(secondary_dir, filename)
            if isfile(metadata_path):
                with open(metadata_path) as f:
                    match = re.match(jar_size_regex, f.read())
                    assert match is not None
                    jar_sizes[i] = int(match.group(1))
                os.remove(metadata_path)
                log("found jar " + filename + " of size " + str(jar_sizes[i]))
            else:
                break

        with open(concat_jar, "rb") as cj:
            for i in dex_order:
                jarpath = join(dex_dir, self._store_name + "-%d.dex.jar" % i)
                with open(jarpath, "wb") as jar:
                    jar.write(cj.read(jar_sizes[i]))

        for j in list(jar_sizes.keys()):
            jar_size = getsize(
                dex_dir + "/" + self._store_name + "-" + str(j) + ".dex.jar"
            )
            log(
                "validating "
                + self._store_name
                + "-"
                + str(j)
                + ".dex.jar size="
                + str(jar_size)
                + " expecting="
                + str(jar_sizes[j])
            )
            assert jar_sizes[j] == jar_size

        assert sum(jar_sizes.values()) == getsize(concat_jar)

        # Clean up everything other than dexen in the dex directory
        os.remove(concat_jar)
        os.remove(dest)

        # Lastly, unzip all the jar files and delete them
        for jarpath in abs_glob(dex_dir, "*.jar"):
            extract_dex_from_jar(jarpath, jarpath[:-4])
            os.remove(jarpath)
        BaseDexMode.unpackage(self, extracted_apk_dir, dex_dir)

    def repackage(
        self,
        extracted_apk_dir: str,
        dex_dir: str,
        have_locators: bool,
        locator_store_id: int = 0,
        fast_repackage: bool = False,
        reset_timestamps: bool = True,
    ) -> None:
        BaseDexMode.repackage(
            self,
            extracted_apk_dir,
            dex_dir,
            have_locators,
            locator_store_id,
            fast_repackage,
            reset_timestamps,
        )

        dex_sizes = {}
        jar_sizes = {}

        concat_jar_path = join(dex_dir, self._store_name + ".dex.jar")
        concat_jar_meta = join(dex_dir, "metadata.txt")
        dex_metadata = DexMetadata(
            have_locators=have_locators,
            store=self._store_id,
            dependencies=self._dependencies,
            locator_store_id=locator_store_id,
        )

        with open(concat_jar_path, "wb") as concat_jar:
            for i in itertools.count(1):
                oldpath = join(dex_dir, self._dex_prefix + "%d.dex" % (i + 1))
                if not isfile(oldpath):
                    break
                dexpath = join(dex_dir, self._store_name + "-%d.dex" % i)

                # Package each dex into a jar
                shutil.move(oldpath, dexpath)
                jarpath = dexpath + ".jar"
                create_dex_jar(jarpath, dexpath, reset_timestamps=reset_timestamps)
                dex_sizes[jarpath] = getsize(dexpath)
                jar_sizes[jarpath] = getsize(jarpath)

                # Concatenate the jar files and create corresponding metadata files
                with open(jarpath + ".xzs.tmp~.meta", "w") as metadata:
                    sizes = "jar:{} dex:{}".format(
                        jar_sizes[jarpath], dex_sizes[jarpath]
                    )
                    metadata.write(sizes)

                with open(jarpath, "rb") as jar:
                    contents = jar.read()
                    concat_jar.write(contents)
                    sha1hash = hashlib.sha1(contents).hexdigest()

                dex_metadata.add_dex(
                    jarpath + ".xzs.tmp~",
                    BaseDexMode.get_canary(self, i),
                    hash=sha1hash,
                )

        dex_metadata.write(concat_jar_meta)
        assert getsize(concat_jar_path) == sum(
            getsize(x) for x in abs_glob(dex_dir, self._store_name + "-*.dex.jar")
        )

        # XZ-compress the result
        pack_xz(
            input=concat_jar_path,
            output=f"{concat_jar_path}.xz",
            compression_level=0 if fast_repackage else 9,
        )
        # Delete the original.
        os.remove(concat_jar_path)

        # Copy all the archive and metadata back to the apk directory
        secondary_dex_dir = join(extracted_apk_dir, self._xzs_dir)
        for path in abs_glob(dex_dir, self._store_name + "*.meta"):
            shutil.copy(path, secondary_dex_dir)
        shutil.copy(concat_jar_meta, join(secondary_dex_dir, "metadata.txt"))
        shutil.copy(
            concat_jar_path + ".xz", join(secondary_dex_dir, self._xzs_filename)
        )


# These are checked in order from top to bottom. The first one to have detect()
# return true will be used.
SECONDARY_DEX_MODES = [
    XZSDexMode(),
    SubdirDexMode(),
    RawSubdirDexMode(),
    Api21DexMode(),
]
BUNDLE_SECONDARY_DEX_MODES = [
    XZSDexMode(
        primary_dir="base/dex",
        secondary_dir="base/assets/secondary-program-dex-jars",
    ),
    SubdirDexMode(
        primary_dir="base/dex",
        secondary_dir="base/assets/secondary-program-dex-jars",
    ),
    RawSubdirDexMode(
        primary_dir="base/dex",
        secondary_dir="base/assets/secondary-program-dex-jars",
    ),
    Api21DexMode(
        primary_dir="base/dex",
        secondary_dir="base/assets/secondary-program-dex-jars",
    ),
]


class UnknownSecondaryDexModeException(Exception):
    pass


def detect_secondary_dex_mode(
    extracted_apk_dir: str, is_bundle: bool = False
) -> BaseDexMode:
    modes = BUNDLE_SECONDARY_DEX_MODES if is_bundle else SECONDARY_DEX_MODES
    for mode in modes:
        if mode.detect(extracted_apk_dir):
            return mode
    raise UnknownSecondaryDexModeException()


def extract_dex_from_jar(jarpath: str, dexpath: str) -> None:
    dest_directory = dirname(dexpath)
    with zipfile.ZipFile(jarpath) as jar:
        contents = jar.namelist()
        dexfiles = [name for name in contents if name.endswith(".dex")]
        assert len(dexfiles) == 1, "Expected a single dex file"
        dexname = jar.extract(dexfiles[0], dest_directory)
        os.rename(join(dest_directory, dexname), dexpath)


def create_dex_jar(
    jarpath: str,
    dexpath: str,
    compression: int = zipfile.ZIP_STORED,
    reset_timestamps: bool = True,
) -> None:
    with zipfile.ZipFile(jarpath, mode="w") as zf:
        zf.write(dexpath, "classes.dex", compress_type=compression)
        zf.writestr(
            "/META-INF/MANIFEST.MF",
            b"Manifest-Version: 1.0\n"
            b"Dex-Location: classes.dex\n"
            b"Created-By: redex\n\n",
        )
    if reset_timestamps:
        ZipReset.reset_file(jarpath)


def count_files_recursive(directory: str) -> int:
    return sum(len(files) for _, _, files in os.walk(directory))


class ZipManager:
    """
    __enter__: Unzips input_apk into extracted_apk_dir
    __exit__: Zips extracted_apk_dir into output_apk
    """

    per_file_compression: typing.Dict[str, int] = {}
    renamed_files_to_original: typing.Dict[str, str] = {}

    def __init__(self, input_apk: str, extracted_apk_dir: str, output_apk: str) -> None:
        self.input_apk = input_apk
        self.extracted_apk_dir = extracted_apk_dir
        self.output_apk = output_apk

    def __enter__(self) -> None:
        log("Extracting apk...")
        # Check for file case issues, complain loudly if the file system
        # unpacked to does not seem to gracefully handle the casing of .apk file
        # contents.
        file_count = count_files_recursive(self.extracted_apk_dir)
        file_casing_dict = defaultdict(set)
        with zipfile.ZipFile(self.input_apk) as z:
            expected_files = len(z.infolist())
            for info in z.infolist():
                self.per_file_compression[info.filename] = info.compress_type
                file_casing_dict[info.filename.lower()].add(info.filename)
            z.extractall(self.extracted_apk_dir)

        file_count = count_files_recursive(self.extracted_apk_dir) - file_count
        if expected_files != file_count:
            detail_str = ""
            for v in file_casing_dict.values():
                if len(v) > 1:
                    detail_str += "\n{ "
                    detail_str += ", ".join(v)
                    detail_str += " }"
            if len(detail_str) > 0:
                raise RuntimeError(
                    "ZipManager did not unpack expected number of files; is this a case insensitive file system? Potentially conflicting files:{}".format(
                        detail_str
                    )
                )

    def set_resource_file_mapping(self, path: str) -> None:
        with open(path) as f:
            mapping = json.load(f)
            for k, v in mapping.items():
                self.renamed_files_to_original[v] = k

    def __exit__(self, *args: typing.Any) -> None:
        remove_signature_files(self.extracted_apk_dir)
        if isfile(self.output_apk):
            os.remove(self.output_apk)

        log("Creating output apk")
        with zipfile.ZipFile(self.output_apk, "w") as new_apk:
            # Need sorted output for deterministic zip file. Sorting `dirnames` will
            # ensure the tree walk order. Sorting `filenames` will ensure the files
            # inside the tree.
            # This scheme uses less memory than collecting all files first.
            for dirpath, dirnames, filenames in os.walk(self.extracted_apk_dir):
                dirnames.sort()
                for filename in sorted(filenames):
                    filepath = join(dirpath, filename)
                    archivepath = filepath[len(self.extracted_apk_dir) + 1 :]
                    try:
                        original_path = self.renamed_files_to_original.get(
                            archivepath, archivepath
                        )
                        compress = self.per_file_compression[original_path]
                    except KeyError:
                        compress = zipfile.ZIP_DEFLATED
                    new_apk.write(filepath, archivepath, compress_type=compress)


class UnpackManager:
    """
    __enter__: Unpacks dexes and application modules from extracted_apk_dir into dex_dir
    __exit__: Repacks the dexes and application modules in dex_dir back into extracted_apk_dir
    """

    application_modules: typing.List[ApplicationModule] = []

    def __init__(
        self,
        input_apk: str,
        extracted_apk_dir: str,
        dex_dir: str,
        have_locators: bool = False,
        debug_mode: bool = False,
        fast_repackage: bool = False,
        reset_timestamps: bool = True,
        is_bundle: bool = False,
    ) -> None:
        self.input_apk = input_apk
        self.extracted_apk_dir = extracted_apk_dir
        self.dex_dir = dex_dir
        self.have_locators = have_locators
        self.debug_mode = debug_mode
        self.fast_repackage = fast_repackage
        self.reset_timestamps: bool = reset_timestamps or debug_mode
        self.is_bundle = is_bundle
        self.dex_mode: typing.Optional[BaseDexMode] = None

    def __enter__(self) -> typing.List[str]:
        dex_mode = detect_secondary_dex_mode(self.extracted_apk_dir, self.is_bundle)
        self.dex_mode = dex_mode
        log("Unpacking dex files")
        dex_mode.unpackage(self.extracted_apk_dir, self.dex_dir)

        log("Detecting Application Modules")
        store_metadata_dir = make_temp_dir(
            ".application_module_metadata", self.debug_mode
        )
        self.application_modules = ApplicationModule.detect(
            self.extracted_apk_dir, self.is_bundle
        )
        store_files = []
        for module in self.application_modules:
            canary_prefix = module.get_canary_prefix()
            log(
                "found module: "
                + module.get_name()
                + " "
                + (canary_prefix if canary_prefix is not None else "(no canary prefix)")
            )
            store_path = os.path.join(self.dex_dir, module.get_name())
            os.mkdir(store_path)
            module.unpackage(self.extracted_apk_dir, store_path)
            store_metadata = os.path.join(
                store_metadata_dir, module.get_name() + ".json"
            )
            module.write_redex_metadata(store_path, store_metadata)
            store_files.append(store_metadata)
        return store_files

    def __exit__(self, *args: typing.Any) -> None:
        log("Repacking dex files")
        log("Emit Locator Strings: %s" % self.have_locators)

        dex_mode = self.dex_mode
        assert dex_mode is not None
        dex_mode.repackage(
            self.extracted_apk_dir,
            self.dex_dir,
            self.have_locators,
            locator_store_id=0,
            fast_repackage=self.fast_repackage,
            reset_timestamps=self.reset_timestamps,
        )

        locator_store_id = 1
        for module in self.application_modules:
            log(
                "repacking module: "
                + module.get_name()
                + " with id "
                + str(locator_store_id)
            )
            module.repackage(
                self.extracted_apk_dir,
                self.dex_dir,
                self.have_locators,
                locator_store_id,
                fast_repackage=self.fast_repackage,
                reset_timestamps=self.reset_timestamps,
            )
            locator_store_id = locator_store_id + 1


class LibraryManager:
    """
    __enter__: Unpacks additional libraries in extracted_apk_dirs so library class files can be found
    __exit__: Cleanup temp directories used by the class
    """

    temporary_libs_dir: typing.Optional[str] = None

    def __init__(self, extracted_apk_dir: str, is_bundle: bool = False) -> None:
        self.extracted_apk_dir = extracted_apk_dir
        self.is_bundle = is_bundle

    def __enter__(self) -> None:
        # Some of the native libraries can be concatenated together into one
        # xz-compressed file. We need to decompress that file so that we can scan
        # through it looking for classnames.
        libs_to_extract = []
        xz_lib_name = "libs.xzs"
        zstd_lib_name = "libs.zstd"
        for root, _, filenames in os.walk(self.extracted_apk_dir):
            for filename in fnmatch.filter(filenames, xz_lib_name):
                libs_to_extract.append(join(root, filename))
            for filename in fnmatch.filter(filenames, zstd_lib_name):
                fullpath = join(root, filename)
                # For voltron modules BUCK creates empty zstd files for each module
                if os.path.getsize(fullpath) > 0:
                    libs_to_extract.append(fullpath)
        if len(libs_to_extract) > 0:
            libs_dir = (
                join(self.extracted_apk_dir, "base", "lib")
                if self.is_bundle
                else join(self.extracted_apk_dir, "lib")
            )
            extracted_dir = join(libs_dir, "__extracted_libs__")
            # Ensure all directories exist.
            self.temporary_libs_dir = ensure_libs_dir(libs_dir, extracted_dir)
            for i, lib_to_extract in enumerate(libs_to_extract):
                extract_path = join(extracted_dir, "lib_{}.so".format(i))
                if lib_to_extract.endswith(xz_lib_name):
                    unpack_xz(lib_to_extract, extract_path)
                else:
                    subprocess.check_call(
                        ["zstd", "-d", lib_to_extract, "-o", extract_path]
                    )

    def __exit__(self, *args: typing.Any) -> None:
        # This dir was just here so we could scan it for classnames, but we don't
        # want to pack it back up into the apk
        temp_libs_dir = self.temporary_libs_dir
        if temp_libs_dir is not None:
            shutil.rmtree(temp_libs_dir)


DateType = typing.Tuple[int, int, int, int, int, int]


# Utility class to reset zip entry timestamps on-the-fly without repackaging.
# Is restricted to single-archive 32-bit zips (like APKs).
class ZipReset:
    @staticmethod
    def reset_array_like(
        inout: typing.Union[bytearray, mmap.mmap],
        size: int,
        date: DateType = (1985, 2, 1, 0, 0, 0),
    ) -> None:
        eocd_len: int = 22
        eocd_signature: typing.ByteString = b"\x50\x4b\x05\x06"
        max_comment_len: int = 65535
        max_eocd_search: int = max_comment_len + eocd_len
        lfh_signature: typing.ByteString = b"\x50\x4b\x03\x04"
        cde_signature: typing.ByteString = b"\x50\x4b\x01\x02"
        cde_len: int = 46
        # A410000
        time_code: int = date[3] << 11 | date[4] << 5 | date[5]
        date_code: int = (date[0] - 1980) << 9 | date[1] << 5 | date[2]

        def short_le(start: int) -> int:
            return int.from_bytes(inout[start : start + 2], byteorder="little")

        def long_le(start: int) -> int:
            return int.from_bytes(inout[start : start + 4], byteorder="little")

        def put_short_le(start: int, val: int) -> None:
            inout[start : start + 2] = val.to_bytes(2, byteorder="little")

        def find_eocd_index(len: int) -> typing.Optional[int]:
            from_index = len - max_eocd_search if len > max_eocd_search else 0
            for i in range(len - 3, from_index - 1, -1):
                if inout[i : i + 4] == eocd_signature:
                    return i
            return None

        def rewrite_entry(index: int) -> int:
            # CDE first.
            assert (
                inout[index : index + 4] == cde_signature
            ), "Did not find CDE signature"
            file_name_len = short_le(index + 28)
            extra_len = short_le(index + 30)
            file_comment_len = short_le(index + 32)
            lfh_index = long_le(index + 42)
            # LFH now.
            assert (
                inout[lfh_index : lfh_index + 4] == lfh_signature
            ), "Did not find LFH signature"

            # Update times.
            put_short_le(index + 12, time_code)
            put_short_le(index + 14, date_code)
            put_short_le(lfh_index + 10, time_code)
            put_short_le(lfh_index + 12, date_code)

            return index + cde_len + file_name_len + extra_len + file_comment_len

        assert size >= eocd_len, "File too small to be a zip"
        eocd_index = find_eocd_index(size)
        assert eocd_index is not None, "Dit not find EOCD"
        assert eocd_index + eocd_len <= size, "EOCD truncated?"

        disk_num = short_le(eocd_index + 4)
        disk_w_cd = short_le(eocd_index + 6)
        num_entries = short_le(eocd_index + 8)
        total_entries = short_le(eocd_index + 10)
        cd_offset = long_le(eocd_index + 16)

        assert (
            disk_num == 0 and disk_w_cd == 0 and num_entries == total_entries
        ), "Archive span unsupported"

        index = cd_offset
        for _i in range(0, total_entries):
            index = rewrite_entry(index)

        assert index == eocd_index, "Failed to reach EOCD again"

    @staticmethod
    def reset_file_into_bytes(
        filename: str, date: DateType = (1980, 1, 1, 0, 0, 0)
    ) -> bytearray:
        with open(filename, "rb") as f:
            data = bytearray(f.read())
        ZipReset.reset_array_like(data, len(data), date)
        return data

    @staticmethod
    def reset_file(filename: str, date: DateType = (1985, 2, 1, 0, 0, 0)) -> None:
        with open(filename, "r+b") as f:
            with mmap.mmap(f.fileno(), 0) as map:
                ZipReset.reset_array_like(map, map.size(), date)
                map.flush()
            os.fsync(f.fileno())
