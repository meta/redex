# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

if (NOT Redex_FOUND)
  set(REDEX_ROOT "" CACHE PATH "Path to the Redex install directory")

  set(REDEX_INCLUDE_SEARCH_DIRS "")
  set(REDEX_LIBRARY_SEARCH_DIRS "")
  if (REDEX_ROOT)
    list(APPEND REDEX_INCLUDE_SEARCH_DIRS "${REDEX_ROOT}/include")
    list(APPEND REDEX_LIBRARY_SEARCH_DIRS "${REDEX_ROOT}/lib")
  endif()

  find_path(REDEX_INCLUDE_DIR
    NAMES redex/libredex/IRCode.h
    HINTS ${REDEX_INCLUDE_SEARCH_DIRS}
    DOC "Path to the Redex include directory")

  find_library(REDEX_LIBREDEX_LIB
    NAMES redex
    HINTS ${REDEX_LIBRARY_SEARCH_DIRS}
    DOC "Path to the Redex library")

  find_library(REDEX_LIBRESOURCE_LIB
    NAMES resource
    HINTS ${REDEX_LIBRARY_SEARCH_DIRS}
    DOC "Path to the Redex resource library")

  find_library(REDEX_LIBTOOL_LIB
    NAMES tool
    HINTS ${REDEX_LIBRARY_SEARCH_DIRS}
    DOC "Path to the Redex tool library")

  include(FindPackageHandleStandardArgs)
  find_package_handle_standard_args(Redex
    REQUIRED_VARS
      REDEX_INCLUDE_DIR
      REDEX_LIBREDEX_LIB
      REDEX_LIBRESOURCE_LIB
      REDEX_LIBTOOL_LIB
    FAIL_MESSAGE
      "Could NOT find Redex. Please provide -DREDEX_ROOT=/path/to/redex")

  if (Redex_FOUND)
    add_library(Redex::LibResource UNKNOWN IMPORTED)
    set(libresource_includes
      "${REDEX_INCLUDE_DIR}/redex/util"
      "${REDEX_INCLUDE_DIR}/redex/libresource")
    set_target_properties(Redex::LibResource PROPERTIES
      IMPORTED_LOCATION "${REDEX_LIBRESOURCE_LIB}"
      INTERFACE_INCLUDE_DIRECTORIES "${libresource_includes}")
    target_link_libraries(Redex::LibResource INTERFACE ZLIB::ZLIB Boost::iostreams)

    add_library(Redex::LibRedex UNKNOWN IMPORTED)
    set(libredex_includes
      "${REDEX_INCLUDE_DIR}/redex/libredex"
      "${REDEX_INCLUDE_DIR}/redex/service/type-analysis"
      "${REDEX_INCLUDE_DIR}/redex/util"
      "${REDEX_INCLUDE_DIR}/redex/shared"
      "${REDEX_INCLUDE_DIR}/redex/sparta")
    set_target_properties(Redex::LibRedex PROPERTIES
      IMPORTED_LOCATION "${REDEX_LIBREDEX_LIB}"
      INTERFACE_INCLUDE_DIRECTORIES "${libredex_includes}")
    target_link_libraries(Redex::LibRedex INTERFACE Redex::LibResource)

    add_library(Redex::LibTool UNKNOWN IMPORTED)
    set(libtool_includes
      "${REDEX_INCLUDE_DIR}/redex/tools/common"
      "${REDEX_INCLUDE_DIR}/redex/tools/tool")
    set_target_properties(Redex::LibTool PROPERTIES
      IMPORTED_LOCATION "${REDEX_LIBTOOL_LIB}"
      INTERFACE_INCLUDE_DIRECTORIES "${libtool_includes}")
    target_link_libraries(Redex::LibTool INTERFACE Redex::LibResource Redex::LibRedex)
  endif()
endif()