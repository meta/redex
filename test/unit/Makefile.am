include $(top_srcdir)/Makefile.inc
include $(top_srcdir)/test/Makefile.inc

ANDROID_SDK = @ANDROID_SDK@
ANDROID_PLATFORM_VERSION = @ANDROID_PLATFORM_VERSION@

AM_CXXFLAGS = --std=gnu++20
AM_CPPFLAGS = $(COMMON_INCLUDES) $(COMMON_TEST_INCLUDES)

# Boost.
AM_CPPFLAGS += $(BOOST_CPPFLAGS)
AM_LDFLAGS = $(BOOST_LDFLAGS)

LDADD = $(COMMON_TEST_LIBS)

# Need to set "sdk_path" environment variable to point to the SDK.
# Need to set "android_target" for the platform version.
# Set any env that a test wants if a test.env file is found.
LOG_COMPILER = sh
AM_LOG_FLAGS = -c 'if [ -f $$0.env ] ; then . ./$$0.env ; fi ; sdk_path=$(ANDROID_SDK) android_target=$(ANDROID_PLATFORM_VERSION) ./$$0'

# make_env: Simple helper to generate test-specific env.
#
# $1: test name
# $2: space-separated list of env values
#
# Use: $(eval $(call make_env,test_name,a=b c=d))
define make_env

$(1).env:
	rm -f $$@
	$(foreach pair,$(2), echo "export $(pair)" >> $$@ ;)

endef

####
# Actual test definitions
####

check_PROGRAMS = \
    aliased_registers_test \
    analysis_usage_test \
    api_utils_test \
    armv7_jit_loop_checker_test \
    array_propagation_test \
    arsc_attribution_test \
    art_profile_writer_pass_test \
    assert_test \
    atomic_field_updater_lowering_test \
    atomic_map_test \
    baseline_profile_test \
    blaming_escape_test \
    block_offset_sink_test \
    boxed_boolean_propagation_test \
    branch_prefix_hoisting_test \
    bridge_synth_inline_pass_test \
    call_site_summary_reductions_test \
    callsite_never_inline_cloning_end_to_end_test \
    callsite_never_inline_cloning_test \
    cfg_inliner_test \
    cfg_mutation_test \
    cfg_positions_test \
    chrome_trace_writer_test \
    class_checker_test \
    class_merging_hot_cold_grouping_test \
    class_order_sample_test \
    check_breadcrumbs_test \
    check_cast_analysis_test \
    clinit_batching_pass_test \
    concurrent_containers_test \
    concurrent_hashtable_test \
    configurable_test \
    config_files_test \
    constructor_analysis_test \
    control_flow_test \
    copy_propagation_test \
    cpp_util_test \
    cse_test \
    creators_test \
    debug_info_test \
    debug_test \
    dedup_blocks_test \
    deobfuscated_alias_test \
    deterministic_containers_test \
    dex_annotation_test \
    dex_class_test \
    dex_hasher_test \
    dex_instruction_test \
    dex_loader_test \
    dex_mutate_test \
    dex_output_test \
    dex_store_test \
    dexvt_test \
    dex_structure_test \
    dex_type_environment_test \
    dex_util_test \
    dominators_test \
    ev_arg_test \
    ev_write_test \
    evaluate_type_checks_test \
    exception_test \
    extract_native_test \
    fast_reg_alloc_test \
    fbjni_marker_test \
    final_inline_v2_test \
    fp_ev_test \
    global_type_analysis_test \
    graph_util_test \
    hierarchy_util_test \
    hot_callsites_test \
    init_class_test \
    init_class_pruner_test \
    init_class_lowering_pass_test \
    instruction_sequence_outliner_test \
    int_type_patcher_test \
    interprocedural_constant_propagation_test \
    ipcp_stringbuilder_append_chain_test \
    intraprocedural_constant_propagation_test \
    ir_assembler_test \
    ir_code_test \
    ir_instruction_test \
    ir_list_test \
    ir_typechecker_test \
    jar_loader_test \
    java_parser_util_test \
    kotlin_lambda_analyzer_test \
    kotlin_lambda_dedup_pass_test \
    literals_test \
    live_range_test \
    local_dce_test \
    local_pointers_test \
    loop_info_test \
    loosen_access_modifier_test \
    match_flow_test \
    match_test \
    materialize_null_checks_test \
    method_inline_test \
    method_profiles_test \
    method_splitting_test \
    method_splitter_test_fixture_test \
    method_splitter_suffix_net_gate_test \
    method_util_test \
    metrics_sink_test \
    monitor_count_test \
    mutf8_compare_test \
    leb_test \
    native_test \
    native_names_test \
    never_compile_selection_test \
    never_inline_eligibility_test \
    null_propagation_test \
    object_inliner_test \
    object_propagation_test \
    optimize_enums_test \
    outliner_type_analysis_test \
    partial_pass_test \
    peephole_test \
    position_interning_test \
    position_map_reader_test \
    print_kotlin_stats_test \
    proguard_lexer_test \
    proguard_map_test \
    proguard_matcher_test \
    proguard_parser_test \
    proguard_print_configuration_test \
    proguard_regex_test \
    pure_analysis_test \
    random_forest_test \
    reachable_natives_test \
    reaching_definitions_test \
    rearrange_enum_clinit_test \
    reduce_array_literals_test \
    reduce_boolean_branches_test \
    reduce_gotos_test \
    reduce_sparse_switches_test \
    reflection_analysis_test \
    reg_alloc_test \
    registers_test \
    remark_test \
    remove_null_check_string_arg_test \
    remove_recursive_locks_test \
    remove_redundant_check_casts_test \
    remove_uninstantiables_test \
    remove_unused_args_test \
    removed_reachability_graph_test \
    renamer_test \
    resolver_test \
    resolve_proguard_value_test \
    resource_inlining_test \
    resource_value_merging \
    resources_test \
    result_propagation_test \
    side_effects_summary_test \
    signed_constant_propagation_test \
    compact_pointer_vector_test \
    source_blocks_test \
    source_debug_extension_test \
    split_net_saving_test \
    synthetic_block_counts_test \
    split_huge_switch_test \
    static_field_dependency_graph_test \
    static_relo_v2_test \
    stringbuilder_append_chain_test \
    stringbuilder_outline_test \
    strip_debug_info_test \
    string_switch_test \
    string_switch_transform_test \
    switch_dispatch_test \
    switch_equiv_test \
    throw_propagation_test \
    rare_suffix_selection_test \
    rare_suffix_method_splitting_test \
    timer_test \
    trace_multithreading_test \
    true_virtuals_test \
    type_analysis_transform_test \
    type_inference_test \
    type_ref_updater_test \
    type_reference_test \
    type_system_test \
    type_util_test \
    unique_method_tracker_test \
    up_code_motion_test \
    used_vars_test \
    virtual_merging_test \
    virtual_scopes_test \
    walkers_test \
    work_queue_test \
    xstorerefs_test \
    string_tree_test

aliased_registers_test_SOURCES = AliasedRegistersTest.cpp

analysis_usage_test_SOURCES = AnalysisUsageTest.cpp

api_utils_test_SOURCES = ApiUtilsTest.cpp ScopeHelper.cpp
api_utils_test_LDADD = $(COMMON_MOCK_TEST_LIBS)
EXTRA_api_utils_test_DEPENDENCIES = api_utils_test.env
$(eval $(call make_env,api_utils_test,api_utils_easy_input_path=$(srcdir)/api_utils_easy_input.txt))

armv7_jit_loop_checker_test_SOURCES = Armv7JitLoopCheckerTest.cpp
armv7_jit_loop_checker_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

array_propagation_test_SOURCES = constant-propagation/ArrayPropagationTest.cpp
array_propagation_test_CPPFLAGS = $(AM_CPPFLAGS) -I$(top_srcdir)/sparta/test

arsc_attribution_test_SOURCES = ArscAttributionTest.cpp $(top_srcdir)/tools/arsc/ArscStats.cpp arsc/TestStructures.cpp
arsc_attribution_test_CPPFLAGS = $(AM_CPPFLAGS) -I$(top_srcdir)/tools/arsc -I$(top_srcdir)/test/unit/arsc

art_profile_writer_pass_test_SOURCES = ArtProfileWriterPassTest.cpp

assert_test_SOURCES = AssertTest.cpp

atomic_field_updater_lowering_test_SOURCES = AtomicFieldUpdaterLoweringTest.cpp

atomic_stat_counter_test_SOURCES = AtomicStatCounterTest.cpp

baseline_profile_test_SOURCES = BaselineProfileTest.cpp

blaming_escape_test_SOURCES = BlamingEscapeTest.cpp

block_offset_sink_test_SOURCES = BlockOffsetSinkTest.cpp
blaming_escape_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

boxed_boolean_propagation_test_SOURCES = constant-propagation/BoxedBooleanPropagationTest.cpp

branch_prefix_hoisting_test_SOURCES = BranchPrefixHoistingTest.cpp ScopeHelper.cpp

bridge_synth_inline_pass_test_SOURCES = BridgeSynthInlinePassTest.cpp

call_site_summary_reductions_test_SOURCES = CallSiteSummaryReductionsTest.cpp

callsite_never_inline_cloning_end_to_end_test_SOURCES = \
    CallsiteNeverInlineCloningEndToEndTest.cpp

callsite_never_inline_cloning_test_SOURCES = \
    CallsiteNeverInlineCloningTest.cpp

cfg_inliner_test_SOURCES = CFGInlinerTest.cpp
cfg_inliner_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

cfg_mutation_test_SOURCES = CFGMutationTest.cpp
cfg_mutation_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

cfg_positions_test_SOURCES = CFGPositionsTest.cpp
cfg_positions_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

chrome_trace_writer_test_SOURCES = ChromeTraceWriterTest.cpp

check_breadcrumbs_test_SOURCES = CheckBreadCrumbsTest.cpp

check_cast_analysis_test_SOURCES = CheckCastAnalysisTest.cpp

class_order_sample_test_SOURCES = ClassOrderSampleTest.cpp

clinit_batching_pass_test_SOURCES = ClinitBatchingPassTest.cpp
EXTRA_clinit_batching_pass_test_DEPENDENCIES = clinit_batching_pass_test.env
$(eval $(call make_env,clinit_batching_pass_test,manifest=$(srcdir)/../integ/ClinitBatchingTestManifest.xml))

class_checker_test_SOURCES = ClassCheckerTest.cpp ScopeHelper.cpp

class_merging_hot_cold_grouping_test_SOURCES = \
    ClassMergingHotColdGroupingTest.cpp ScopeHelper.cpp

concurrent_containers_test_SOURCES = ConcurrentContainersTest.cpp

concurrent_hashtable_test_SOURCES = ConcurrentHashtableTest.cpp

atomic_map_test_SOURCES = AtomicMapTest.cpp

configurable_test_SOURCES = ConfigurableTest.cpp
configurable_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

config_files_test_SOURCES = ConfigFilesTest.cpp
EXTRA_config_files_test_DEPENDENCIES = config_files_test.env
$(eval $(call make_env,config_files_test,class_frequencies_path=$(srcdir)/class_frequencies.txt))

constructor_analysis_test_SOURCES = ConstructorAnalysisTest.cpp

control_flow_test_SOURCES = ControlFlowTest.cpp
control_flow_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

copy_propagation_test_SOURCES = CopyPropagationTest.cpp

cpp_util_test_SOURCES = CppUtilTest.cpp
cpp_util_test_LDADD = $(COMMON_MOCK_TEST_LIBS) -lpthread

cse_test_SOURCES = CommonSubexpressionEliminationTest.cpp
cse_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

creators_test_SOURCES = CreatorsTest.cpp

debug_info_test_SOURCES = DebugInfoTest.cpp

debug_test_SOURCES = DebugTest.cpp

dedup_blocks_test_SOURCES = DedupBlocksTest.cpp VirtScopeHelper.cpp ScopeHelper.cpp

deobfuscated_alias_test_SOURCES = DeobfuscatedAliasTest.cpp

deterministic_containers_test_SOURCES = DeterministicContainersTest.cpp
deterministic_containers_test_LDADD = $(COMMON_MOCK_TEST_LIBS) -lpthread

dex_annotation_test_SOURCES = DexAnnotationTest.cpp

dex_class_test_SOURCES = DexClassTest.cpp

dex_hasher_test_SOURCES = DexHasherTest.cpp

dex_instruction_test_SOURCES = DexInstructionTest.cpp

dex_loader_test_SOURCES = DexLoaderTest.cpp

dex_mutate_test_SOURCES = DexMutateTest.cpp

dex_output_test_SOURCES = DexOutputTest.cpp

dex_store_test_SOURCES = DexStoreTest.cpp

dex_structure_test_SOURCES = DexStructureTest.cpp

dexvt_test_SOURCES = DexVtTest.cpp

dex_type_environment_test_SOURCES = type-analysis/DexTypeEnvironmentTest.cpp

dex_util_test_SOURCES = DexUtilTest.cpp

dominators_test_SOURCES = DominatorsTest.cpp

ev_arg_test_SOURCES = EvArgTest.cpp

ev_write_test_SOURCES = EvWriteTest.cpp

evaluate_type_checks_test_SOURCES = EvaluateTypeChecksTest.cpp

exception_test_SOURCES = RedexExceptionTest.cpp

extract_native_test_SOURCES = ExtractNativeTest.cpp

fast_reg_alloc_test_SOURCES = FastRegAllocTest.cpp

fbjni_marker_test_SOURCES = FbjniMarkerTest.cpp
EXTRA_fbjni_marker_test_DEPENDENCIES = fbjni_marker_test.env
$(eval $(call make_env,fbjni_marker_test,test_fbjni_json=$(srcdir)/example_fbjni.json))

final_inline_v2_test_SOURCES = FinalInlineV2Test.cpp

fp_ev_test_SOURCES = FpEvTest.cpp

global_type_analysis_test_SOURCES = type-analysis/GlobalTypeAnalysisTest.cpp

graph_util_test_SOURCES = GraphUtilTest.cpp

hierarchy_util_test_SOURCES = HierarchyUtilTest.cpp

hot_callsites_test_SOURCES = HotCallsitesTest.cpp
hierarchy_util_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

hot_cold_method_specializing_test_SOURCES = HotColdMethodSpecializingTest.cpp

init_class_test_SOURCES = InitClassTest.cpp

init_class_pruner_test_SOURCES = InitClassPrunerTest.cpp

init_class_lowering_pass_test_SOURCES = InitClassLoweringPassTest.cpp

unreachable_lowering_pass_test_SOURCES = UnreachableLoweringPassTest.cpp

int_type_patcher_test_SOURCES = IntTypePatcherTest.cpp

instruction_sequence_outliner_test_SOURCES = InstructionSequenceOutlinerTest.cpp ScopeHelper.cpp

interprocedural_constant_propagation_test_SOURCES = constant-propagation/IPConstantPropagationTest.cpp

ipcp_stringbuilder_append_chain_test_SOURCES = constant-propagation/IPCPStringBuilderAppendChainTest.cpp

intraprocedural_constant_propagation_test_SOURCES = constant-propagation/ConstantPropagationTest.cpp
intraprocedural_constant_propagation_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

ir_assembler_test_SOURCES = IRAssemblerTest.cpp

ir_code_test_SOURCES = IRCodeTest.cpp

ir_instruction_test_SOURCES = IRInstructionTest.cpp OpcodeList.cpp

ir_list_test_SOURCES = IRListTest.cpp
ir_list_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

ir_typechecker_test_SOURCES = IRTypeCheckerTest.cpp
ir_typechecker_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

jar_loader_test_SOURCES = JarLoaderTest.cpp

java_parser_util_test_SOURCES = JavaParserUtilTest.cpp
java_parser_util_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

kotlin_lambda_analyzer_test_SOURCES = KotlinLambdaAnalyzerTest.cpp
kotlin_lambda_analyzer_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

kotlin_lambda_dedup_pass_test_SOURCES = KotlinLambdaDeduplicationPassTest.cpp
kotlin_lambda_dedup_pass_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

literals_test_SOURCES = LiteralsTest.cpp

live_range_test_SOURCES = LiveRangeTest.cpp
live_range_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

local_dce_test_SOURCES = LocalDceTest.cpp ScopeHelper.cpp

local_pointers_test_SOURCES = LocalPointersTest.cpp
local_pointers_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

loop_info_test_SOURCES = LoopInfoTest.cpp
loop_info_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

loosen_access_modifier_test_SOURCES = LoosenAccessModifierTest.cpp

match_test_SOURCES = MatchTest.cpp

match_flow_test_SOURCES = MatchFlowTest.cpp
match_flow_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

materialize_null_checks_test_SOURCES = MaterializeNullChecksTest.cpp

method_inline_test_SOURCES = MethodInlineTest.cpp

method_profiles_test_SOURCES = MethodProfilesTest.cpp

tail_duplication_test_SOURCES = TailDuplicationTest.cpp

method_splitting_test_SOURCES = MethodSplittingTest.cpp

method_splitter_test_fixture_test_SOURCES = \
	MethodSplitterTestFixture.cpp \
	MethodSplitterTestFixtureTest.cpp

method_splitter_suffix_net_gate_test_SOURCES = \
	MethodSplitterTestFixture.cpp \
	MethodSplitterSuffixNetGateTest.cpp

method_util_test_SOURCES = MethodUtilTest.cpp

metrics_sink_test_SOURCES = MetricsSinkTest.cpp

monitor_count_test_SOURCES = MonitorCountTest.cpp

mutf8_compare_test_SOURCES = Mutf8CompareTest.cpp

leb_test_SOURCES = LebTest.cpp

native_test_SOURCES = NativeTest.cpp
native_test_LDADD = $(COMMON_MOCK_TEST_LIBS)
EXTRA_native_test_DEPENDENCIES = native_test.env
$(eval $(call make_env,native_test,native_jni_output_path=$(srcdir)))

native_names_test_SOURCES = NativeNamesTest.cpp

never_compile_selection_test_SOURCES = NeverCompileSelectionTest.cpp

never_inline_eligibility_test_SOURCES = NeverInlineEligibilityTest.cpp

nopper_test_SOURCES = NopperTest.cpp

null_propagation_test_SOURCES = constant-propagation/NullPropagationTest.cpp

object_inliner_test_SOURCES = ObjectInlinerTest.cpp
object_inliner_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

object_propagation_test_SOURCES = constant-propagation/ObjectPropagationTest.cpp
object_propagation_test_CPPFLAGS = $(AM_CPPFLAGS) -I$(top_srcdir)/sparta/test

optimize_enums_test_SOURCES = OptimizeEnumsTest.cpp
optimize_enums_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

outliner_type_analysis_test_SOURCES = OutlinerTypeAnalysisTest.cpp

partial_pass_test_SOURCES = PartialPassTest.cpp

peephole_test_SOURCES = PeepholeTest.cpp

position_interning_test_SOURCES = PositionInterningTest.cpp

position_map_reader_test_SOURCES = PositionMapReaderTest.cpp \
	$(top_srcdir)/tools/debug-info/PositionMap.cpp
position_map_reader_test_CPPFLAGS = $(AM_CPPFLAGS) -I$(top_srcdir)/tools/debug-info

print_kotlin_stats_test_SOURCES = PrintKotlinStatsTest.cpp

proguard_lexer_test_SOURCES = ProguardLexerTest.cpp

proguard_map_test_SOURCES = ProguardMapTest.cpp
proguard_map_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

proguard_matcher_test_SOURCES = ProguardMatcherTest.cpp

proguard_parser_test_SOURCES = ProguardParserTest.cpp
proguard_parser_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

proguard_print_configuration_test_SOURCES = ProguardPrintConfigurationTest.cpp

proguard_regex_test_SOURCES = ProguardRegexTest.cpp

pure_analysis_test_SOURCES = PureAnalysisTest.cpp
pure_analysis_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

random_forest_test_SOURCES = RandomForestTest.cpp

reachable_natives_test_SOURCES = ReachableNativesTest.cpp
reachable_natives_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

reaching_definitions_test_SOURCES = ReachingDefinitionsTest.cpp

rearrange_enum_clinit_test_SOURCES = RearrangeEnumClinitTest.cpp

reduce_array_literals_test_SOURCES = ReduceArrayLiteralsTest.cpp
reduce_array_literals_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

reduce_boolean_branches_test_SOURCES = ReduceBooleanBranchesTest.cpp VirtScopeHelper.cpp ScopeHelper.cpp
reduce_boolean_branches_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

reduce_gotos_test_SOURCES = ReduceGotosTest.cpp
reduce_gotos_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

reduce_sparse_switches_test_SOURCES = ReduceSparseSwitchesTest.cpp

reflection_analysis_test_SOURCES = ReflectionAnalysisTest.cpp
reflection_analysis_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

reg_alloc_test_SOURCES = RegAllocTest.cpp OpcodeList.cpp
reg_alloc_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

registers_test_SOURCES = RegistersTest.cpp OpcodeList.cpp

remark_test_SOURCES = RemarkTest.cpp

remove_null_check_string_arg_test_SOURCES = RemoveNullCheckStringArgTest.cpp ScopeHelper.cpp

remove_recursive_locks_test_SOURCES = RemoveRecursiveLocksTest.cpp

remove_redundant_check_casts_test_SOURCES = RemoveRedundantCheckCastsTest.cpp VirtScopeHelper.cpp ScopeHelper.cpp

remove_uninstantiables_test_SOURCES = RemoveUninstantiablesTest.cpp ScopeHelper.cpp
remove_uninstantiables_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

remove_unused_args_test_SOURCES = RemoveUnusedArgsTest.cpp ScopeHelper.cpp
remove_unused_args_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

removed_reachability_graph_test_SOURCES = RemovedReachabilityGraphTest.cpp
removed_reachability_graph_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

renamer_test_SOURCES = RenamerTest.cpp VirtScopeHelper.cpp ScopeHelper.cpp

resolver_test_SOURCES = ResolverTest.cpp
resolve_proguard_value_test_SOURCES = ResolveProguardAssumeValuesTest.cpp ScopeHelper.cpp

resource_inlining_test_SOURCES = ResourceInliningTest.cpp ScopeHelper.cpp arsc/TestStructures.cpp

resource_value_merging_SOURCES = ResourceValueMergingPassTest.cpp
resource_value_merging_LDADD = $(COMMON_MOCK_TEST_LIBS)

result_propagation_test_SOURCES = ResultPropagationTest.cpp
result_propagation_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

side_effects_summary_test_SOURCES = object-sensitive-dce/SideEffectSummaryTest.cpp
side_effects_summary_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

signed_constant_propagation_test_SOURCES = constant-propagation/SignedConstantPropagationTest.cpp
signed_constant_propagation_test_CPPFLAGS = $(AM_CPPFLAGS) -I$(top_srcdir)/sparta/test

compact_pointer_vector_test_SOURCES = CompactPointerVectorTest.cpp

source_blocks_test_SOURCES = SourceBlocksTest.cpp

source_debug_extension_test_SOURCES = SourceDebugExtensionTest.cpp

split_net_saving_test_SOURCES = SplitNetSavingTest.cpp

synthetic_block_counts_test_SOURCES = SyntheticBlockCountsTest.cpp

split_huge_switch_test_SOURCES = SplitHugeSwitchTest.cpp

static_field_dependency_graph_test_SOURCES = StaticFieldDependencyGraphTest.cpp

static_relo_v2_test_SOURCES = StaticReloV2Test.cpp

stringbuilder_append_chain_test_SOURCES = constant-propagation/StringBuilderAppendChainTest.cpp

stringbuilder_outline_test_SOURCES = StringBuilderOutlinerTest.cpp

string_propagation_test_SOURCES = constant-propagation/StringPropagationTest.cpp

strip_debug_info_test_SOURCES = StripDebugInfoTest.cpp

switch_dispatch_test_SOURCES = SwitchDispatchTest.cpp

string_switch_test_SOURCES = StringSwitchFinderTest.cpp
string_switch_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

string_switch_transform_test_SOURCES = StringSwitchTransformTest.cpp
string_switch_transform_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

switch_equiv_test_SOURCES = SwitchEquivFinderTest.cpp
switch_equiv_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

throw_propagation_test_SOURCES = ThrowPropagationTest.cpp
throw_propagation_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

rare_suffix_selection_test_SOURCES = RareSuffixSelectionTest.cpp

rare_suffix_method_splitting_test_SOURCES = RareSuffixMethodSplittingTest.cpp

timer_test_SOURCES = TimerTest.cpp

trace_multithreading_test_SOURCES = TraceMultithreadingTest.cpp
trace_multithreading_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

true_virtuals_test_SOURCES = TrueVirtualsTest.cpp ScopeHelper.cpp
true_virtuals_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

type_analysis_transform_test_SOURCES = type-analysis/TypeAnalysisTransformTest.cpp

type_inference_test_SOURCES = TypeInferenceTest.cpp
type_inference_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

type_ref_updater_test_SOURCES = TypeRefUpdaterTest.cpp

type_reference_test_SOURCES = TypeReferenceTest.cpp

type_system_test_SOURCES = TypeSystemTest.cpp ScopeHelper.cpp
type_system_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

type_util_test_SOURCES = TypeUtilTest.cpp

unique_method_tracker_test_SOURCES = UniqueMethodTrackerTest.cpp
unique_method_tracker_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

up_code_motion_test_SOURCES = UpCodeMotionTest.cpp
up_code_motion_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

used_vars_test_SOURCES = object-sensitive-dce/UsedVarsTest.cpp
used_vars_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

virtual_merging_test_SOURCES = VirtualMergingTest.cpp

virtual_scopes_test_SOURCES = VirtualScopesTest.cpp ScopeHelper.cpp
virtual_scopes_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

walkers_test_SOURCES = WalkersTest.cpp
walkers_test_LDADD = $(COMMON_MOCK_TEST_LIBS)

work_queue_test_SOURCES = WorkQueueTest.cpp

xstorerefs_test_SOURCES = XStoreRefsTest.cpp

string_tree_test_SOURCES = StringTreeTest.cpp

resources_test_SOURCES = RedexResourcesTest.cpp
resources_test_LDADD = $(COMMON_MOCK_TEST_LIBS)
EXTRA_resources_test_DEPENDENCIES = resources_test.env more_resources/res/layout/class_names.xml
$(eval $(call make_env,resources_test,\
  test_layout_path=$(srcdir)/example_layout_with_onclick.xml \
  another_layout_path=more_resources/res/layout/class_names.xml \
  single_resource_inclusion_path=$(srcdir)/example_single_resource_to_keep.xml \
  multiple_resource_inclusion_path=$(srcdir)/example_multiple_resource_to_keep.xml \
  empty_resource_inclusion_path=$(srcdir)/example_no_resource_to_keep.xml))

more_resources/res/layout/class_names.xml:
	mkdir -p more_resources && unzip ../samples/more_resources/unsigned.apk -d more_resources res/layout/class_names.xml

TESTS = $(check_PROGRAMS)
