#!/bin/bash
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

TERMUX_TMP=""
if pwd | grep -q "termux"; then
TERMUX_TMP="/data/data/com.termux/cache"
mkdir -p $TERMUX_TMP/tmp
fi

export TMPDIR=`mktemp -d "$TERMUX_TMP/tmp/redex.XXXXXX"`
ARCHIVE=`awk '/^__ARCHIVE_BELOW__/ { print NR + 1; exit 0 }' $0`
tail -n+$ARCHIVE $0 | tar xz -C $TMPDIR

$TMPDIR/redex.py $@

rm -rf $TMPDIR
exit 0

__ARCHIVE_BELOW__
