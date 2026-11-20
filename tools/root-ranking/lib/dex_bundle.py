# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

"""The DEX files an APK or app bundle carries.

Most DEX files are plain `.dex` entries: `classes2.dex` in an APK,
`<module>/dex/classes2.dex` in an app bundle. Secondary DEX files may also sit
in `assets/secondary-program-dex-jars/` as `.dex.jar` archives, which are read
through, or in compressed stores such as `.dex.jar.xzs`, which are not: those are
reported, so a missing DEX file is never silently absent from a result.
"""

from __future__ import annotations

import io
import posixpath
import zipfile
from dataclasses import dataclass

_IN_JAR = "!/"


@dataclass(frozen=True)
class DexInventory:
    dexes: list[str]  # entry names; `<jar>!/<dex>` inside a .dex.jar
    unread: list[str]  # DEX stores this reader does not open


def inventory(bundle: str) -> DexInventory:
    dexes: list[str] = []
    unread: list[str] = []
    with zipfile.ZipFile(bundle) as archive:
        for entry in archive.namelist():
            base = posixpath.basename(entry)
            if base.endswith(".dex"):
                dexes.append(entry)
            elif base.endswith(".dex.jar"):
                with zipfile.ZipFile(io.BytesIO(archive.read(entry))) as jar:
                    dexes += [
                        entry + _IN_JAR + name
                        for name in jar.namelist()
                        if name.endswith(".dex")
                    ]
            elif ".dex." in base and not base.endswith((".meta", ".txt")):
                unread.append(entry)
    return DexInventory(dexes, unread)


def read_dex(bundle: str, name: str) -> bytes:
    outer, _, inner = name.partition(_IN_JAR)
    with zipfile.ZipFile(bundle) as archive:
        data = archive.read(outer)
    if not inner:
        return data
    # Buck writes each secondary `.dex.jar` with a single `classes.dex`, so
    # `read_dex` reads each jar once per DEX it holds: once.
    with zipfile.ZipFile(io.BytesIO(data)) as jar:
        return jar.read(inner)


def store_of(name: str) -> str:
    """The module a DEX entry belongs to: an app bundle's top directory; in an
    APK, `assets/<module>/` for modules and `base` for the rest."""
    top, slash, rest = name.partition("/")
    if top == "assets":
        module, slash, _ = rest.partition("/")
        return module if slash and module != "secondary-program-dex-jars" else "base"
    if not slash or top in ("lib", "res", "root"):
        return "base"
    return top
