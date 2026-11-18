# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import json
import os
import tempfile
import unittest
from unittest import mock

from pyredex.unpacker import ApplicationModule


class WriteRedexMetadataTest(unittest.TestCase):
    def write_metadata(self, listed: list[str]) -> list[str]:
        module = ApplicationModule("/apk", "feature", None, [], "")
        with tempfile.TemporaryDirectory() as tmp:
            metadata_file = os.path.join(tmp, "feature.json")
            with mock.patch(
                "glob.glob", return_value=[f"/dex/feature/{d}" for d in listed]
            ):
                module.write_redex_metadata("/dex/feature", metadata_file)
            with open(metadata_file) as f:
                return [os.path.basename(p) for p in json.load(f)["files"]]

    def test_classes_dexes_in_dex_order(self) -> None:
        self.assertEqual(
            self.write_metadata(["classes10.dex", "classes2.dex", "classes.dex"]),
            ["classes.dex", "classes2.dex", "classes10.dex"],
        )

    def test_numbered_dexes_in_dex_order(self) -> None:
        self.assertEqual(
            self.write_metadata(["feature-10.dex", "feature-2.dex", "feature-1.dex"]),
            ["feature-1.dex", "feature-2.dex", "feature-10.dex"],
        )

    def test_store_named_dexes_in_dex_order(self) -> None:
        self.assertEqual(
            self.write_metadata(["feature10.dex", "feature2.dex", "feature.dex"]),
            ["feature.dex", "feature2.dex", "feature10.dex"],
        )

    def test_ambiguous_dex_order_rejected(self) -> None:
        with self.assertRaisesRegex(Exception, "Ambiguous dex order"):
            self.write_metadata(["classes.dex", "feature-1.dex"])
