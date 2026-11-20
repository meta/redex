# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

import io
import os
import tempfile
import unittest
import zipfile

from root_ranking.dex_bundle import inventory, read_dex, store_of


class DexBundleTest(unittest.TestCase):
    def test_reads_plain_and_jarred_dexes_and_reports_compressed_stores(self):
        jar = io.BytesIO()
        with zipfile.ZipFile(jar, "w") as inner:
            inner.writestr("classes.dex", b"jarred")
        with tempfile.TemporaryDirectory() as temp_dir:
            bundle = os.path.join(temp_dir, "app.apk")
            with zipfile.ZipFile(bundle, "w") as outer:
                outer.writestr("classes.dex", b"plain")
                outer.writestr(
                    "assets/secondary-program-dex-jars/s1.dex.jar", jar.getvalue()
                )
                outer.writestr("assets/secondary-program-dex-jars/s.dex.jar.xzs", b"")
                outer.writestr("assets/secondary-program-dex-jars/s.dex.jar.meta", b"")
            dexes = inventory(bundle)
            self.assertEqual(
                [
                    "classes.dex",
                    "assets/secondary-program-dex-jars/s1.dex.jar!/classes.dex",
                ],
                dexes.dexes,
            )
            self.assertEqual(
                ["assets/secondary-program-dex-jars/s.dex.jar.xzs"], dexes.unread
            )
            self.assertEqual(b"jarred", read_dex(bundle, dexes.dexes[1]))

    def test_store_is_the_bundle_module(self):
        self.assertEqual("base", store_of("classes2.dex"))
        self.assertEqual(
            "base", store_of("assets/secondary-program-dex-jars/s.dex.jar")
        )
        self.assertEqual("feature", store_of("feature/dex/classes.dex"))
        self.assertEqual("module", store_of("assets/module/m1.dex.jar!/classes.dex"))
