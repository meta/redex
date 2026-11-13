/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.facebook.redex.test.instr;

import static org.assertj.core.api.Assertions.assertThat;

import com.facebook.FooTextView;
import org.junit.Test;

interface IForceRename {

}

class CantRename {
}

class ForceRename implements IForceRename {
}

public class RenameClassesV2Test {

  @Test
  public void testRenames() {
    // Make sure CantRename's name is not changed
    assertThat(CantRename.class.getName()).isEqualTo(
        Utils.demangle("com_facebook_redex_test_instr_CantRename"));
    // Make sure ForceRename's name /is/ changed
    assertThat(ForceRename.class.getName()).isNotEqualTo(
        Utils.demangle("com_facebook_redex_test_instr_ForceRename"));
    // Make sure, specifically, that it seems to abide the renamer's conventions
    assertThat(ForceRename.class.getPackage().getName()).isEqualTo("X");
    assertThat(FooTextView.class.getPackage().getName()).isEqualTo("X");
  }

  // ForceRename[][] and IForceRename[][] are referenced here, but neither
  // one-dimensional array type is referenced anywhere in this app. The
  // two-dimensional array types must still follow their renamed classes.
  @Test
  public void testRenamesArrayTypeWithoutLowerDimension() {
    Object array = new ForceRename[1][1];
    assertThat(array instanceof IForceRename[][]).isTrue();
  }
}
