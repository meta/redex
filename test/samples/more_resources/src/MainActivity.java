/*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

package com.fb.resources;

import android.content.res.Resources;
import com.facebook.R;

import android.app.Activity;
import android.os.Bundle;

public class MainActivity extends Activity {

  private static final String LOG_TAG = "REDEX";

  @Override
  protected void onCreate(Bundle savedInstanceState) {
    super.onCreate(savedInstanceState);
    setContentView(R.layout.activity_main);
    logValues();
  }

  private void logValues() {
    Resources resources = getResources();
    if (resources.getBoolean(R.bool.should_log)) {
      int simple = resources.getColor(R.color.simple);
      android.util.Log.w(LOG_TAG, "simple: " + Integer.toHexString(simple));

      int txt = resources.getColor(R.color.text_color);
      android.util.Log.w(LOG_TAG, "text_color: " + Integer.toHexString(txt));

      int bg = resources.getColor(R.color.view_bg);
      android.util.Log.w(LOG_TAG, "view_bg: " + Integer.toHexString(bg));

      int purple = resources.getColor(R.color.nice_purple);

      int count = resources.getInteger(R.integer.loop_count);
      String main = resources.getString(R.string.main_text);
      for (int i = 0; i < count; i++) {
        android.util.Log.w(LOG_TAG, "main_text: " + main + " [" + (i + 1) + " / " + count + "]");
      }

      String styled_text = resources.getString(R.string.styled_text);
      android.util.Log.w(LOG_TAG, "styled_text: " + styled_text);

      int size = resources.getDimensionPixelSize(R.dimen.text_size);
      android.util.Log.w(LOG_TAG, "Text size (in pixels): " + size);

      int bool_int = resources.getInteger(R.bool.should_log);
      android.util.Log.w(LOG_TAG, "bool_int: " + Integer.toHexString(bool_int));

      String string_color = resources.getString(R.color.nice_purple);
      android.util.Log.w(LOG_TAG, "string_color: " + string_color);

      String string_int = resources.getString(R.integer.loop_count);
      android.util.Log.w(LOG_TAG, "string_int: " + string_int);

      String res_name = resources.getResourceName(R.integer.loop_count); 
      android.util.Log.w(LOG_TAG, "res_name: " + res_name);

      String res_entry_name = resources.getResourceEntryName(R.integer.loop_count); 
      android.util.Log.w(LOG_TAG, "res_entry_name: " + res_entry_name);
    }
  }

  private void crazy() {
    System.out.println(R.color.simple + 1);
    System.out.println((long)R.string.styled_text);
    Resources resources = getResources();
    System.out.println(R.dimen.text_size / 2);
    System.out.println(R.dimen.text_size / resources.getInteger(R.integer.loop_count));
    System.out.println(resources.getBoolean(R.bool.should_log));
  }
}
