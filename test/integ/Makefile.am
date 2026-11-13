include $(top_srcdir)/Makefile.inc
include $(top_srcdir)/test/Makefile.inc

D8 = @D8@

ANDROID_JAR = @ANDROID_JAR@
ANDROID_SDK = @ANDROID_SDK@
ANDROID_PLATFORM_VERSION = @ANDROID_PLATFORM_VERSION@

AM_CXXFLAGS = --std=gnu++20
AM_CPPFLAGS = $(COMMON_INCLUDES) $(COMMON_TEST_INCLUDES)

# Boost.
AM_CPPFLAGS += $(BOOST_CPPFLAGS)
AM_LDFLAGS = $(BOOST_LDFLAGS)

LDADD = $(COMMON_MOCK_TEST_LIBS)

# Need to set "dexfile" environment variable to point to the dex file ised in
# the test. We do this with a helper script and naming convention.
LOG_COMPILER = sh
AM_LOG_FLAGS = -c 'sdk_path=$(ANDROID_SDK) android_target=$(ANDROID_PLATFORM_VERSION) dexfile=$$0-class.dex ./$$0'

check_PROGRAMS = \
    app_module_usage_test \
    call_graph_test \
    clinit_side_effect_test \
    constant_propagation_test \
    constructor_dedup_test_test \
    copy_prop_test \
    dedup_blocks_test \
    dedup_vmethods_test \
    default_annotation_test \
    dex_output_test \
    final_inline_analysis_test \
    global_type_analysis_test \
    instruction_sequence_outliner_test \
    iodi_test \
    ip_reflection_analysis_test \
    lift_vmethods_test \
    method_override_graph_test \
    monotonic_fixpoint_test \
    partial_application_test \
    peephole_test \
    points_to_semantics_test \
    propagation_test \
    pure_method_test \
    r_class_test \
    reachability_test \
    reflection_analysis_test \
    resolve_refs_test \
    remove_unreachable_test \
    result_propagation_test \
    strip_debug_info_test \
    type_analysis_transform_test \
    type_inference_test \
    uses_app_module_annotation_test \
    verifier_artifacts_test

if RUN_KOTLIN_TESTS
# Add Kotlin tests here.
check_PROGRAMS += \
    bitwise_ops_constant_propagation_test \
    kotlin_default_args_test \
    recursive_bitset_constant_propagation_test \
    remove_redundant_nullcheck
endif

# As CircleCI treats XFAIL tests as fails, we need to exclude failing
# tests explicitly.
#
# XFAIL_TESTS = \
#     app_module_usage_test \
#     copy_prop_test \
#     dex_output_test \
#     global_type_analysis_test \
#     instruction_sequence_outliner_test \
#     monotonic_fixpoint_test \
#     partial_application_test \
#     resolve_refs_test \
#     type_inference_test

TESTS = \
    call_graph_test \
    clinit_side_effect_test \
    constant_propagation_test \
    constructor_dedup_test_test \
    dedup_blocks_test \
    dedup_vmethods_test \
    default_annotation_test \
    final_inline_analysis_test \
    iodi_test \
    ip_reflection_analysis_test \
    lift_vmethods_test \
    method_override_graph_test \
    peephole_test \
    points_to_semantics_test \
    propagation_test \
    pure_method_test \
    r_class_test \
    reachability_test \
    reflection_analysis_test \
    remove_unreachable_test \
    result_propagation_test \
    strip_debug_info_test \
    type_analysis_transform_test \
    uses_app_module_annotation_test \
    verifier_artifacts_test

if RUN_KOTLIN_TESTS
# Add Kotlin tests here.
TESTS += \
    bitwise_ops_constant_propagation_test \
    kotlin_default_args_test \
    recursive_bitset_constant_propagation_test \
    remove_redundant_nullcheck
endif

app_module_usage_test_SOURCES = AppModuleUsageTest.cpp
EXTRA_app_module_usage_test_DEPNDENCIES = uses_app_module_annotation-class.dex app_module_usage_test-class.dex app_module_usage_test_other-class.dex app_module_usage_test_third-class.dex

call_graph_test_SOURCES = CallGraphTest.cpp
EXTRA_call_graph_test_DEPENDENCIES = call_graph_test-class.dex

clinit_side_effect_test_SOURCES = ClinitSideEffect.cpp
EXTRA_clinit_side_effect_test_DEPENDENCIES = clinit_side_effect_test-class.dex

constant_propagation_test_SOURCES = ConstantPropagationTest.cpp
EXTRA_constant_propagation_test_DEPENDENCIES = constant_propagation_test-class.dex

constructor_dedup_test_test_SOURCES = ConstructorDedupTest.cpp
EXTRA_constructor_dedup_test_test_DEPENDENCIES = constructor_dedup_test_test-class.dex

copy_prop_test_SOURCES = CopyPropagationTest.cpp
EXTRA_copy_prop_test_DEPENDENCIES = copy_prop_test-class.dex

dedup_blocks_test_SOURCES = DedupBlocksTest.cpp
EXTRA_dedup_blocks_test_DEPENDENCIES = dedup_blocks_test-class.dex

dedup_vmethods_test_SOURCES = DedupVirtualMethodsTest.cpp
EXTRA_dedup_vmethods_test_DEPENDENCIES = dedup_vmethods_test-class.dex

default_annotation_test_SOURCES = DefaultAnnotation.cpp
EXTRA_default_annotation_test_DEPENDENCIES = default_annotation_test-class.dex

dex_output_test_SOURCES = DexOutputTest.cpp
EXTRA_dex_output_test_DEPENDENCIES = dex_output_test-class.dex

final_inline_analysis_test_SOURCES = FinalInlineAnalysisTest.cpp
EXTRA_final_inline_analysis_test_DEPENDENCIES = final_inline_analysis_test-class.dex

access_marking_test_SOURCES = AccessMarkingTest.cpp
EXTRA_access_marking_test_DEPENDENCIES = access_marking_test-class.dex

global_type_analysis_test_SOURCES = GlobalTypeAnalysisTest.cpp
EXTRA_global_type_analysis_test_DEPENDENCIES = global_type_analysis_test-class.dex

instruction_sequence_outliner_test_SOURCES = InstructionSequenceOutlinerTest.cpp
EXTRA_instruction_sequence_outliner_test_DEPENDENCIES = instruction_sequence_outliner_test-class.dex

iodi_test_SOURCES = IODI.cpp
EXTRA_iodi_test_DEPENDENCIES = iodi_test-class.dex

ip_reflection_analysis_test_SOURCES = IPReflectionAnalysisTest.cpp
EXTRA_ip_reflection_analysis_test_DEPENDENCIES = ip_reflection_analysis_test-class.dex

lift_vmethods_test_SOURCES = LiftVirtualMethodsTest.cpp
EXTRA_lift_vmethods_test_DEPENDENCIES = lift_vmethods_test-class.dex

method_override_graph_test_SOURCES = MethodOverrideGraphTest.cpp
EXTRA_method_override_graph_test_DEPENDENCIES = method_override_graph_test-class.dex

monotonic_fixpoint_test_SOURCES = MonotonicFixpointTest.cpp
EXTRA_monotonic_fixpoint_test_DEPENDENCIES = monotonic_fixpoint_test-class.dex

r_class_test_SOURCES = RClassTest.cpp
EXTRA_r_class_test_DEPENDENCIES = r_class_test-class.dex

partial_application_test_SOURCES = PartialApplicationTest.cpp
EXTRA_partial_application_test_DEPENDENCIES = partial_application_test-class.dex

peephole_test_SOURCES = PeepholeTest.cpp
EXTRA_peephole_test_DEPENDENCIES = peephole_test-class.dex

points_to_semantics_test_SOURCES = PointsToSemanticsTest.cpp
EXTRA_points_to_semantics_test_DEPENDENCIES = points_to_semantics_test-class.dex

propagation_test_SOURCES = PropagationTest.cpp
EXTRA_propagation_test_DEPENDENCIES = propagation_test-class.dex

pure_method_test_SOURCES = PureFunctionTest.cpp
EXTRA_pure_method_test_DEPENDENCIES = pure_method_test-class.dex

reachability_test_SOURCES = ReachabilityTest.cpp
EXTRA_reachability_test_DEPENDENCIES = reachability_test-class.dex

reflection_analysis_test_SOURCES = ReflectionAnalysisTest.cpp
EXTRA_reflection_analysis_test_DEPENDENCIES = reflection_analysis_test-class.dex

resolve_refs_test_SOURCES = ResolveRefsTest.cpp
EXTRA_resolve_refs_test_DEPENDENCIES = resolve_refs_test-class.dex

remove_unreachable_test_SOURCES = RemoveUnreachableTest.cpp
EXTRA_remove_unreachable_test_DEPENDENCIES = remove_unreachable_test-class.dex

result_propagation_test_SOURCES = ResultPropagationTest.cpp
EXTRA_result_propagation_test_DEPENDENCIES = result_propagation_test-class.dex

strip_debug_info_test_SOURCES = StripDebugInfoTest.cpp
EXTRA_strip_debug_info_test_DEPENDENCIES = strip_debug_info_test-class.dex

type_analysis_transform_test_SOURCES = TypeAnalysisTransformTest.cpp
EXTRA_type_analysis_transform_test_DEPENDENCIES = type_analysis_transform_test-class.dex

type_inference_test_SOURCES = TypeInferenceTest.cpp
EXTRA_type_inference_test_DEPENDENCIES = type_inference_test-class.dex

uses_app_module_annotation_test_SOURCES = UsesAppModuleTest.cpp
EXTRA_uses_app_module_annotation_test_DEPENDENCIES = uses_app_module_annotation-class.dex uses_app_module_annotation_test-class.dex app_module_usage_test-class.dex app_module_usage_test_other-class.dex app_module_usage_test_third-class.dex

verifier_artifacts_test_SOURCES = VerifierTest.cpp
EXTRA_verifier_artifacts_test_DEPENDENCIES = verifier_artifacts_test-class.dex

# -parameters works around a D8 bug in the pinned build-tools 29.0.2: javac 21+
# emits a nameless MethodParameters entry for an inner class constructor's
# mandated outer-instance parameter, and that D8 dereferences the null name.
# Naming every parameter avoids it. D8 discards the attribute, so the dex is
# byte-identical either way.
javac_source_target = -source 8 -target 8 -parameters

define create_jar
	mkdir -p $@.tmp
	$(JAVAC) $(javac_source_target) -cp "$(srcdir)" -d $@.tmp $^
	jar cf $@ -C $@.tmp .
endef

SUFFIXES = .dex

.jar.dex:
	rm -rf $@.d8 && $(MKDIR_P) $@.d8
	$(D8) --intermediate --output $@.d8 --lib $(ANDROID_JAR) $^
	mv $@.d8/classes.dex $@
	rm -rf $@.d8

app_module_usage_test-class.jar: AppModuleUsageClass.java
	$(create_jar)

app_module_usage_test_other-class.jar: AppModuleUsageOtherClass.java
	$(create_jar)

app_module_usage_test_third-class.jar: AppModuleUsageThirdClass.java
	$(create_jar)

call_graph_test-class.jar: CallGraphTest.java
	$(create_jar)

clinit_side_effect_test-class.jar: ClinitSideEffect.java
	$(create_jar)

constant_propagation_test-class.jar: ConstantPropagation.java
	$(create_jar)

constructor_dedup_test_test-class.jar: ConstructorDedupTest.java
	$(create_jar)

copy_prop_test-class.jar: CopyPropagationTest.java
	$(create_jar)

dedup_blocks_test-class.jar: DedupBlocksTest.java
	$(create_jar)

dedup_vmethods_test-class.jar: DedupVirtualMethodsTest.java
	$(create_jar)

default_annotation_test-class.jar: DefaultAnnotationTest.java
	$(create_jar)

dex_output_test-class.jar: DexOutputTest.java
	$(create_jar)

final_inline_analysis_test-class.jar: FinalInlineAnalysisTest.java
	$(create_jar)

global_type_analysis_test-class.jar: GlobalTypeAnalysisTest.java
	$(create_jar)

instruction_sequence_outliner_test-class.jar: InstructionSequenceOutlinerTest.java
	$(create_jar)

iodi_test-class.jar: IODI.java
	$(create_jar)

ip_reflection_analysis_test-class.jar: IPReflectionAnalysisTest.java
	$(create_jar)

lift_vmethods_test-class.jar: LiftVirtualMethodsTest.java
	$(create_jar)

method_override_graph_test-class.jar: MethodOverrideGraphTest.java
	$(create_jar)

monotonic_fixpoint_test-class.jar: MonotonicFixpoint.java
	$(create_jar)

r_class_test-class.jar: R.java
	$(create_jar)

partial_application_test-class.jar: PartialApplication.java
	$(create_jar)

peephole_test-class.jar: Peephole.java
	$(create_jar)

points_to_semantics_test-class.jar: PointsToSemantics.java
	$(create_jar)

propagation_test-class.jar: Propagation.java
	$(create_jar)

pure_method_test-class.jar: PureFunctionTest.java
	$(create_jar)

reachability_test-class.jar: RemoveUnreachableTest.java
	$(create_jar)

reflection_analysis_test-class.jar: ReflectionAnalysis.java
	$(create_jar)

resolve_refs_test-class.jar: ResolveRefsTest.java
	$(create_jar)

remove_unreachable_test-class.jar: RemoveUnreachableTest.java
	$(create_jar)

result_propagation_test-class.jar: ResultPropagation.java
	$(create_jar)

strip_debug_info_test-class.jar: StripDebugInfo.java
	$(create_jar)

type_analysis_transform_test-class.jar: TypeAnalysisTransformTest.java
	$(create_jar)

type_inference_test-class.jar: TypeInferenceTest.java
	$(create_jar)

uses_app_module_annotation-class.jar: UsesAppModule.java
	$(create_jar)

uses_app_module_annotation_test-class.jar: UsesAppModuleAnnotated.java
	$(create_jar)

verifier_artifacts_test-class.jar: VerifierTest.java
	$(create_jar)

if RUN_KOTLIN_TESTS
kotlinc_source_target = -jvm-target 9

kotlin_default_args_test_SOURCES = KotlinDefaultArgsTest.cpp
EXTRA_kotlin_default_args_test_DEPENDENCIES = kotlin_default_args_test-class.dex
bitwise_ops_constant_propagation_test_SOURCES = BitwiseOpsConstantPropagationTest.cpp
EXTRA_bitwise_ops_constant_propagation_test_DEPENDENCIES = bitwise_ops_constant_propagation_test-class.dex
recursive_bitset_constant_propagation_test_SOURCES = RecursiveBitsetConstantPropagationTest.cpp
EXTRA_recursive_bitset_constant_propagation_test_DEPENDENCIES = recursive_bitset_constant_propagation_test-class.dex
remove_redundant_nullcheck_SOURCES = TypeAnalysisRemoveRedundantNullCheck.cpp
EXTRA_remove_redundant_nullcheck_DEPENDENCIES = remove_redundant_nullcheck-class.dex

define create_jar_from_kotlin
	mkdir -p $@.tmp
	$(KOTLINC) $(kotlinc_source_target) -cp "$(srcdir)" -d $@.tmp $^
	jar cf $@ -C $@.tmp .
endef

kotlin_default_args_test-class.jar: KotlinDefaultArgs.kt
	$(create_jar_from_kotlin)

bitwise_ops_constant_propagation_test-class.jar: BitwiseOpsConstantPropagationTest.kt
	$(create_jar_from_kotlin)

recursive_bitset_constant_propagation_test-class.jar: RecursiveBitsetConstantPropagation.kt
	$(create_jar_from_kotlin)

remove_redundant_nullcheck-class.jar: TypeAnalysisRemoveRedundantNullCheck.kt
	$(create_jar_from_kotlin)

endif
