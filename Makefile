ROCQ ?= rocq
ROCQFLAGS ?=
SOURCES := theories/AbstractGuard.v theories/SemanticFacts.v theories/DomainRestriction.v theories/ResidualGuard.v \
           theories/AbstractSchedule.v theories/AbstractScheduleChecker.v theories/SchedulePermutation.v theories/EndpointBridge.v theories/BilateralTransport.v \
           theories/SilentRegionProtocol.v \
           theories/PolCertCompat.v \
           theories/GuardedRegion.v theories/CheckedGuard.v theories/Examples.v \
           theories/Presumption.v theories/Synthesis.v theories/ConditionalRewrite.v \
           theories/StatefulGuard.v theories/StatefulGuardComposition.v

.PHONY: all proof demo check fetch-compcert compcert-proof check-compcert compcert-bridge \
        guarded-compiler scheduled-compiler rectangular-compiler stripmine-compiler native-demo native-schedules native-rectangular native-stripmine check-integration polcert-proof polcert-affine-proof polcert-loop-proof \
        polcert-dynamic-proof polcert-nested-proof polcert-memory-proof \
        polcert-optimizer-proof polcert-store-native clean
all: check

proof:
	@mkdir -p build
	@$(ROCQ) --version > build/compiler.txt
	@set -eu; for src in $(SOURCES); do $(ROCQ) compile $(ROCQFLAGS) -Q theories Guard "$$src"; done

.PHONY: interface-proof interface-clight-proof interface-compiler-proof interface-native interface-matrix-native interface-rectangle-native interface-cells-native interface-loops-native interface-private-native interface-stable-load-native interface-loaded-bound-native interface-common-native
interface-proof:
	python3 scripts/audit_interface.py

interface-clight-proof: interface-proof
	python3 scripts/audit_interface_clight.py

interface-compiler-proof: interface-clight-proof
	python3 scripts/audit_interface_compiler.py

interface-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py > build/interface-compiler/build.log 2>&1
	python3 scripts/native_interface_demo.py

interface-matrix-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --matrix > build/interface-compiler/matrix-build.log 2>&1
	python3 scripts/native_interface_matrix.py

interface-rectangle-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --rectangle > build/interface-compiler/rectangle-build.log 2>&1
	python3 scripts/native_interface_rectangle.py

interface-cells-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --cells > build/interface-compiler/cells-build.log 2>&1
	python3 scripts/native_interface_cells.py

interface-loops-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --loops > build/interface-compiler/loops-build.log 2>&1
	python3 scripts/native_interface_loops.py

interface-private-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --private-candidate > build/interface-compiler/private-build.log 2>&1
	python3 scripts/native_interface_private.py

interface-stable-load-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --stable-load > build/interface-compiler/stable-load-build.log 2>&1
	python3 scripts/native_interface_stable_load.py

interface-loaded-bound-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --loaded-bound
	python3 scripts/native_interface_loaded_bound.py

interface-common-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --common
	python3 scripts/native_interface_common.py
	python3 scripts/native_interface_runtime_stride.py --common
	python3 scripts/native_interface_indexed_load.py --common
	python3 scripts/native_interface_indexed_bound.py --common
	python3 scripts/native_interface_equality.py --common
	python3 scripts/native_interface_equality_head.py --common
	python3 scripts/native_interface_loaded_equality.py --common
	python3 scripts/native_interface_loaded_matrix.py --common
	python3 scripts/native_interface_loaded_rectangle.py --common
	python3 scripts/native_interface_loaded_stride.py --common

.PHONY: interface-runtime-stride-native
interface-runtime-stride-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --runtime-stride
	python3 scripts/native_interface_runtime_stride.py

.PHONY: interface-indexed-load-native
interface-indexed-load-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --indexed-load
	python3 scripts/native_interface_indexed_load.py

.PHONY: interface-indexed-bound-native
interface-indexed-bound-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --indexed-bound
	python3 scripts/native_interface_indexed_bound.py

.PHONY: interface-equality-native
interface-equality-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --equality
	python3 scripts/native_interface_equality.py

.PHONY: interface-equality-head-native
interface-equality-head-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --equality-head
	python3 scripts/native_interface_equality_head.py
	python3 scripts/native_interface_loaded_equality.py

.PHONY: interface-loaded-matrix-native
interface-loaded-matrix-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --loaded-matrix
	python3 scripts/native_interface_loaded_matrix.py

.PHONY: interface-loaded-rectangle-native
interface-loaded-rectangle-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --loaded-rectangle
	python3 scripts/native_interface_loaded_rectangle.py

.PHONY: interface-shared-loaded-rectangle-native
interface-shared-loaded-rectangle-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --shared-loaded-rectangle
	python3 scripts/native_interface_loaded_rectangle.py --shared

.PHONY: interface-simplified-rectangle-native
interface-simplified-rectangle-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --simplified-rectangle
	python3 scripts/native_interface_loaded_rectangle.py --simplified

.PHONY: interface-loaded-stride-native
interface-loaded-stride-native: interface-compiler-proof
	python3 scripts/build_interface_compiler.py --loaded-stride
	python3 scripts/native_interface_loaded_stride.py

.PHONY: interface-native-suite
interface-native-suite: interface-native interface-matrix-native interface-rectangle-native interface-cells-native interface-loops-native interface-private-native interface-stable-load-native interface-loaded-bound-native interface-common-native interface-runtime-stride-native interface-indexed-load-native interface-indexed-bound-native interface-equality-native interface-equality-head-native interface-loaded-matrix-native interface-loaded-rectangle-native interface-loaded-stride-native interface-shared-loaded-rectangle-native interface-simplified-rectangle-native

demo:
	python3 prototype/demo.py
	python3 prototype/synthesis_demo.py
	python3 scripts/schedule_checker_demo.py

check: proof demo

COMPCERT_DIR ?= vendor/CompCert
COMPCERT_FLAGS = -R $(COMPCERT_DIR)/lib compcert.lib \
                 -R $(COMPCERT_DIR)/common compcert.common \
                 -R $(COMPCERT_DIR)/x86 compcert.x86 \
                 -R $(COMPCERT_DIR)/x86_64 compcert.x86_64 \
                 -R $(COMPCERT_DIR)/cfrontend compcert.cfrontend \
                 -R $(COMPCERT_DIR)/backend compcert.backend \
                 -R $(COMPCERT_DIR)/driver compcert.driver \
                 -R $(COMPCERT_DIR)/flocq Flocq

BRIDGE_SOURCES := theories/CompCertArithmetic.v theories/ClightPositiveDivision.v theories/CompCertMemoryEquivalence.v \
                  theories/CompCertOperatorEquivalence.v theories/ClightGuard.v theories/ClightSyntaxEquality.v \
                  theories/ClightGuardProof.v theories/ClightEncodedRule.v theories/ClightNoWrap.v \
                  theories/ClightExprRewrite.v theories/ClightExprRewriteProof.v \
                  theories/ClightExprRule.v theories/CommonRewrites.v \
                  theories/CompCertMemoryRule.v \
                  theories/GuardCompiler.v theories/ClightIntegrationExamples.v \
                  theories/CommonRewriteExamples.v theories/ClightCondition.v \
                  theories/ClightMemoryEquivalence.v theories/ClightMemorySteps.v theories/ClightPureExpr.v \
                  theories/ClightIndexGuard.v \
                  theories/ClightCountedLoop.v theories/ClightTempFrame.v theories/ClightFramedLoop.v \
                  theories/ClightWideGuard.v \
                  theories/ClightTreeRewrite.v theories/ClightTreeRewriteProof.v \
                  theories/ClightTreeRule.v theories/ClightDecisionRule.v theories/ClightTreeExamples.v \
                  theories/ClightSameAddress.v theories/ClightSignedCancel.v theories/TreeCompiler.v \
                  theories/ClightFiniteRegion.v theories/ClightRegionProtocol.v \
                  theories/ClightCountedProtocol.v theories/ClightCountedProtocolExamples.v \
                  theories/ClightRegionRewrite.v \
                  theories/ClightRegionRewriteProof.v theories/ClightRegionRule.v theories/ClightStraightLine.v \
                  theories/ClightRedundantSet.v theories/RegionCompiler.v \
                  theories/ClightRegionProgress.v theories/ClightProgressClassifier.v \
                  theories/ClightAdaptiveRegion.v theories/ClightAdaptiveRegionProof.v \
                  theories/ClightZeroTrip.v theories/ClightFrontendLoopProtocol.v theories/ClightFrontendRegion.v \
                  theories/ClightFragmentProgress.v theories/ClightSequenceProgress.v theories/ClightNestedProgress.v \
                  theories/ClightNestedFrontendProgress.v theories/ClightStructuredProgress.v \
                  theories/CompCertStoreSchedule.v theories/CompCertIndexSchedule.v \
                  theories/ClightPositiveCheck.v theories/ClightLoopExecution.v \
                  theories/ClightLoopSyntax.v theories/ClightMatrixStore.v theories/ClightMatrixGuard.v \
                  theories/ClightMatrixLoops.v theories/ClightMatrixRegion.v theories/ClightMatrixSelector.v \
                  theories/AdaptiveRegionCompiler.v theories/ClightAdaptiveExamples.v theories/ClightNestedProgressExamples.v \
                  theories/ClightIndexedStores.v theories/ClightSharedRegion.v \
                  theories/ClightScheduledMatrix.v theories/ScheduledRegionCompiler.v \
                  theories/ScheduleInterleave.v theories/RectangularSchedule.v theories/RectangularIteration.v \
                  theories/ClightParametricLoops.v theories/ClightRectangularStore.v \
                  theories/ClightRectangularLoops.v theories/ClightRectangularGuard.v \
                  theories/ClightRectangularRegion.v theories/ClightRectangularSelector.v \
                  theories/CompCertMemoryActions.v theories/RectangularMemorySchedule.v theories/RectangularRowSchedule.v \
                  theories/ClightRectangularUpdate.v theories/ClightRectangularUpdateRegion.v theories/ClightRectangularUpdateSelector.v \
                  theories/ClightIndexedArray.v theories/ClightRectangularRowUpdate.v theories/ClightRectangularRowRegion.v theories/ClightRectangularRowSelector.v \
                  theories/RectangularCompiler.v \
                  theories/ClightTempFootprint.v theories/ClightTempScope.v theories/ClightProjectedExecution.v \
                  theories/ClightPrivateRegion.v theories/ClightPrivateRegionProof.v theories/ClightPrivatePool.v \
                  theories/ClightPrivateRule.v theories/CountedStripmine.v theories/ClightStripmineLoops.v \
                  theories/ClightStripmineGuard.v theories/ClightStripmineRegion.v theories/ClightStripmineSelector.v \
                  theories/StripmineCompiler.v

compcert-bridge:
	@set -eu; for src in $(BRIDGE_SOURCES); do $(ROCQ) compile $(ROCQFLAGS) -Q theories Guard $(COMPCERT_FLAGS) "$$src"; done

fetch-compcert:
	python3 scripts/fetch_compcert.py

compcert-proof: fetch-compcert
	@mkdir -p build
	@set -eu; cd $(COMPCERT_DIR); \
	  if test ! -f Makefile.config; then ./configure -clightgen x86_64-linux; fi; \
	  if test ! -f .depend; then $(MAKE) depend; fi; \
	  $(MAKE) -j4 proof > ../../build/compcert-proof.log 2>&1 || \
	  { cat ../../build/compcert-proof.log; exit 1; }

check-compcert: check compcert-proof
	$(MAKE) compcert-bridge
	python3 scripts/audit_memory_transport.py
	python3 scripts/audit_region_protocol.py
	python3 scripts/audit_matrix_interchange.py
	python3 scripts/audit_scheduled_matrix.py

guarded-compiler: check-compcert
	python3 scripts/audit_compiler.py
	@python3 scripts/build_compiler.py > build/native-build.log 2>&1 || \
	  { cat build/native-build.log; exit 1; }

native-demo: guarded-compiler
	python3 scripts/native_demo.py
	python3 scripts/native_rewrites.py
	python3 scripts/native_alias.py
	python3 scripts/native_signed.py
	python3 scripts/native_region.py
	python3 scripts/native_zero_trip.py
	python3 scripts/native_nested_regions.py
	python3 scripts/native_matrix_interchange.py

scheduled-compiler: check-compcert
	@python3 scripts/build_compiler.py --matrix-schedule > build/scheduled-native-build.log 2>&1 || \
	  { cat build/scheduled-native-build.log; exit 1; }

native-schedules: scheduled-compiler
	python3 scripts/native_scheduled_matrix.py

check-integration: native-demo native-schedules native-rectangular native-stripmine

rectangular-compiler: check-compcert
	python3 scripts/audit_rectangular.py
	@python3 scripts/build_compiler.py --rectangular-loop > build/rectangular-native-build.log 2>&1 || \
	  { cat build/rectangular-native-build.log; exit 1; }

native-rectangular: rectangular-compiler
	python3 scripts/native_rectangular.py

stripmine-compiler: check-compcert
	python3 scripts/audit_stripmine.py
	@python3 scripts/build_compiler.py --stripmine > build/stripmine-native-build.log 2>&1 || \
	  { cat build/stripmine-native-build.log; exit 1; }

native-stripmine: stripmine-compiler
	python3 scripts/native_stripmine.py

POLCERT_SOURCE ?=
POLCERT_SOURCE_ARG = $(if $(POLCERT_SOURCE),--source "$(POLCERT_SOURCE)",)

polcert-proof: check-compcert
	python3 scripts/polcert_core.py restore $(POLCERT_SOURCE_ARG)
	python3 scripts/polcert_core.py build --clean
	python3 scripts/polcert_core.py adapter

polcert-affine-proof: polcert-proof
	python3 scripts/polcert_core.py affine-adapter

polcert-loop-proof: polcert-affine-proof
	python3 scripts/polcert_core.py counted-adapter

polcert-dynamic-proof: polcert-affine-proof
	python3 scripts/polcert_core.py dynamic-adapter

polcert-nested-proof: polcert-loop-proof
	python3 scripts/polcert_core.py nested-adapter

polcert-memory-proof: check-compcert
	python3 scripts/polcert_core.py restore --profile memory $(POLCERT_SOURCE_ARG)
	python3 scripts/polcert_core.py build --profile memory --target src/CInstr.v --target polygen/Loop.v --clean
	python3 scripts/polcert_core.py memory-adapter --profile memory

polcert-store-native: polcert-memory-proof
	python3 scripts/audit_compiler.py --store-swap
	@python3 scripts/build_compiler.py --store-swap > build/store-swap-native-build.log 2>&1 || \
	  { cat build/store-swap-native-build.log; exit 1; }
	python3 scripts/native_store_swap.py
	python3 scripts/native_dynamic_store.py

polcert-optimizer-proof: check-compcert
	python3 scripts/polcert_core.py restore --profile optimizer $(POLCERT_SOURCE_ARG)
	python3 scripts/polcert_core.py build --profile optimizer --target driver/PolOptCorrect.v --clean
	python3 scripts/polcert_core.py optimizer-adapter --profile optimizer

guard-memory-proof: polcert-optimizer-proof
	python3 scripts/audit_guard_memory.py

.PHONY: guard-memory-proof memory-validator native-memory-validator memory-compiler native-memory-compiler memory-tiling-compiler native-memory-tiling memory-cut-compiler native-memory-cuts
memory-validator: guard-memory-proof
	python3 scripts/build_memory_validator.py

native-memory-validator: memory-validator
	python3 scripts/native_memory_validator.py

memory-compiler: guard-memory-proof
	python3 scripts/build_memory_compiler.py

native-memory-compiler: memory-compiler
	python3 scripts/native_memory_compiler.py

memory-tiling-compiler: guard-memory-proof
	@python3 scripts/build_memory_compiler.py --tiling > build/memory-tiled-native-build.log 2>&1 || \
	  { cat build/memory-tiled-native-build.log; exit 1; }

native-memory-tiling: memory-tiling-compiler
	python3 scripts/native_memory_tiling.py

memory-cut-compiler: guard-memory-proof
	@python3 scripts/build_memory_compiler.py --cuts > build/memory-cut-native-build.log 2>&1 || \
	  { cat build/memory-cut-native-build.log; exit 1; }

native-memory-cuts: memory-cut-compiler
	python3 scripts/native_memory_cuts.py

.PHONY: memory-sequence-compiler native-memory-sequences
memory-sequence-compiler: guard-memory-proof
	@python3 scripts/build_memory_compiler.py --sequences > build/memory-sequence-native-build.log 2>&1 || \
	  { cat build/memory-sequence-native-build.log; exit 1; }

native-memory-sequences: memory-sequence-compiler
	python3 scripts/native_memory_sequences.py

clean:
	@python3 scripts/clean.py

.PHONY: memory-operations-compiler native-memory-operations
memory-operations-compiler: guard-memory-proof
	@python3 scripts/build_memory_compiler.py --operations > build/memory-operations-native-build.log 2>&1 || \
	  { cat build/memory-operations-native-build.log; exit 1; }

native-memory-operations: memory-operations-compiler
	python3 scripts/native_memory_operations.py

.PHONY: native-memory-loop-ir memory-proposed-compiler native-memory-proposed
native-memory-loop-ir: memory-validator
	python3 scripts/native_memory_loop_ir.py

memory-proposed-compiler: guard-memory-proof
	@python3 scripts/build_memory_compiler.py --proposed > build/memory-proposed-native-build.log 2>&1 || \
	  { cat build/memory-proposed-native-build.log; exit 1; }

native-memory-proposed: memory-proposed-compiler
	python3 scripts/native_memory_proposed.py

.PHONY: memory-unified-compiler native-memory-unified
memory-unified-compiler: guard-memory-proof
	@python3 scripts/build_memory_compiler.py --unified > build/memory-unified-native-build.log 2>&1 || \
	  { cat build/memory-unified-native-build.log; exit 1; }

native-memory-unified: memory-unified-compiler
	python3 scripts/native_memory_unified.py

.PHONY: native-memory-multiarray
native-memory-multiarray: memory-unified-compiler
	python3 scripts/native_memory_multiarray.py

.PHONY: native-memory-affine-maps
native-memory-affine-maps: memory-unified-compiler
	python3 scripts/native_memory_affine_maps.py

.PHONY: native-memory-ragged
native-memory-ragged: memory-unified-compiler
	python3 scripts/native_memory_ragged.py

.PHONY: native-memory-schedules
native-memory-schedules: memory-unified-compiler
	python3 scripts/native_memory_schedules.py

.PHONY: native-memory-parametric
native-memory-parametric: memory-unified-compiler
	python3 scripts/native_memory_parametric.py
	python3 scripts/native_memory_parametric_context.py

.PHONY: native-memory-layout-copy
native-memory-layout-copy: memory-unified-compiler
	python3 scripts/native_memory_layout_copy.py

.PHONY: native-memory-layout-sequence
native-memory-layout-sequence: memory-unified-compiler
	python3 scripts/native_memory_layout_sequence.py
	python3 scripts/native_memory_layout_sequence_paths.py

.PHONY: native-memory-affine-access
native-memory-affine-access: memory-unified-compiler
	python3 scripts/native_memory_affine_access.py
	python3 scripts/native_memory_affine_access_paths.py

.PHONY: native-memory-offset-access
native-memory-offset-access: memory-unified-compiler
	python3 scripts/native_memory_offset_access.py
	python3 scripts/native_memory_offset_access_paths.py

.PHONY: native-memory-affine-compute
native-memory-affine-compute: memory-unified-compiler
	python3 scripts/native_memory_affine_compute.py
	python3 scripts/native_memory_affine_compute_paths.py

.PHONY: native-memory-conditioned-width
native-memory-conditioned-width: memory-unified-compiler
	python3 scripts/native_memory_conditioned_width.py
	python3 scripts/native_memory_conditioned_width_paths.py

.PHONY: native-memory-triple
native-memory-triple: memory-unified-compiler
	python3 scripts/native_memory_triple.py
	python3 scripts/native_memory_triple_paths.py

.PHONY: native-memory-recursive
native-memory-recursive: memory-unified-compiler
	python3 scripts/native_memory_recursive.py
	python3 scripts/native_memory_recursive_paths.py

.PHONY: native-memory-pointer
native-memory-pointer: memory-unified-compiler
	python3 scripts/native_memory_pointer.py
	python3 scripts/native_memory_pointer_paths.py

.PHONY: native-memory-scalar
native-memory-scalar: memory-unified-compiler
	python3 scripts/native_memory_scalar.py
	python3 scripts/native_memory_scalar_paths.py

.PHONY: native-memory-scalar-array
native-memory-scalar-array: memory-unified-compiler
	python3 scripts/native_memory_scalar_array.py
	python3 scripts/native_memory_scalar_array_paths.py

.PHONY: native-memory-signed
native-memory-signed: memory-unified-compiler
	python3 scripts/native_memory_signed.py
	python3 scripts/native_memory_signed_paths.py

.PHONY: native-memory-multi-pointer
native-memory-multi-pointer: memory-unified-compiler
	python3 scripts/native_memory_multi_pointer.py
	python3 scripts/native_memory_multi_pointer_paths.py

.PHONY: native-memory-source-metadata
native-memory-source-metadata: memory-unified-compiler
	python3 scripts/native_memory_source_metadata.py
	python3 scripts/native_memory_source_metadata_paths.py

.PHONY: native-memory-loop-alias
native-memory-loop-alias: memory-unified-compiler
	python3 scripts/native_memory_loop_alias.py
	python3 scripts/native_memory_loop_alias_paths.py

.PHONY: native-memory-affine-alias
native-memory-affine-alias: memory-unified-compiler
	python3 scripts/native_memory_affine_alias.py
	python3 scripts/native_memory_affine_alias_paths.py

.PHONY: native-memory-affine-endpoints
native-memory-affine-endpoints: memory-unified-compiler
	python3 scripts/native_memory_affine_endpoints.py
	python3 scripts/native_memory_affine_endpoints_paths.py

.PHONY: native-memory-axis-alias
native-memory-axis-alias: memory-unified-compiler
	python3 scripts/native_memory_axis_alias.py
	python3 scripts/native_memory_axis_alias_paths.py

.PHONY: native-memory-axis-pair-choice
native-memory-axis-pair-choice: native-memory-multi-pointer
	python3 scripts/native_memory_axis_pair_choice_paths.py

.PHONY: native-memory-axis-bounds
native-memory-axis-bounds: memory-unified-compiler
	python3 scripts/native_memory_axis_bounds.py
	python3 scripts/native_memory_axis_bounds_paths.py

.PHONY: native-memory-address-parameters
native-memory-address-parameters: memory-unified-compiler
	python3 scripts/native_memory_address_parameters.py
	python3 scripts/native_memory_address_parameters_paths.py

.PHONY: native-memory-parameter-versions
native-memory-parameter-versions: memory-unified-compiler
	python3 scripts/native_memory_parameter_versions.py
	python3 scripts/native_memory_parameter_versions_paths.py

.PHONY: native-memory-prefilter-versions
native-memory-prefilter-versions: memory-unified-compiler
	python3 scripts/native_memory_parameter_versions.py --prefilter
	python3 scripts/native_memory_parameter_versions_paths.py --prefilter

.PHONY: native-memory-started-regions
native-memory-started-regions: memory-unified-compiler
	python3 scripts/native_memory_started_regions.py
	python3 scripts/native_memory_started_regions_paths.py

.PHONY: native-memory-signed-windows
native-memory-signed-windows: memory-unified-compiler
	python3 scripts/native_memory_signed_windows.py
	python3 scripts/native_memory_signed_windows_paths.py

.PHONY: native-memory-signed-multiple-pointers
native-memory-signed-multiple-pointers: memory-unified-compiler
	python3 scripts/native_memory_signed_multiple_pointers.py
	python3 scripts/native_memory_signed_multiple_pointers_paths.py

.PHONY: affine-nest-prototype-proof
affine-nest-prototype-proof:
	python3 scripts/audit_affine_nest_prototype.py

.PHONY: affine-nest-compiler native-affine-nest native-affine-nest-ranges
affine-nest-compiler:
	python3 scripts/build_affine_nest_compiler.py

native-affine-nest:
	python3 scripts/native_affine_nest.py
	python3 scripts/native_affine_nest_paths.py

native-affine-nest-ranges:
	python3 scripts/native_affine_nest_ranges.py
	python3 scripts/native_affine_nest_ranges_paths.py

.PHONY: guardcert-compiler native-guardcert
guardcert-compiler:
	python3 scripts/build_affine_nest_compiler.py --unified

native-guardcert:
	python3 scripts/native_guardcert.py
	python3 scripts/native_guardcert_paths.py

.PHONY: native-affine-nest-multiple-pointers
native-affine-nest-multiple-pointers:
	python3 scripts/native_affine_nest_multiple_pointers.py
	python3 scripts/native_affine_nest_multiple_pointers_paths.py

.PHONY: native-affine-nest-external
native-affine-nest-external:
	python3 scripts/native_affine_nest_external.py
	python3 scripts/native_affine_nest_external_paths.py

.PHONY: native-affine-nest-fission
native-affine-nest-fission:
	python3 scripts/native_affine_nest_fission.py
	python3 scripts/native_affine_nest_fission_paths.py

.PHONY: guardcert-conditioned-compiler
guardcert-conditioned-compiler:
	python3 scripts/build_affine_nest_compiler.py --conditioned

.PHONY: native-affine-nest-condition-search native-guardcert-conditioned
native-affine-nest-condition-search:
	python3 scripts/native_affine_nest_condition_search.py
	python3 scripts/native_affine_nest_condition_search_paths.py

native-guardcert-conditioned:
	python3 scripts/native_guardcert_conditioned.py

.PHONY: native-affine-nest-domain-split
native-affine-nest-domain-split:
	python3 scripts/native_affine_nest_domain_split.py
	python3 scripts/native_affine_nest_domain_split_paths.py

.PHONY: native-variable-cancel
native-variable-cancel:
	python3 scripts/native_variable_cancel.py
	python3 scripts/native_variable_cancel_paths.py

.PHONY: guardcert-versions-compiler native-affine-nest-runtime-versions
guardcert-versions-compiler:
	python3 scripts/build_affine_nest_compiler.py --versions
native-affine-nest-runtime-versions:
	python3 scripts/native_affine_nest_runtime_versions.py
	python3 scripts/native_affine_nest_runtime_versions_paths.py

.PHONY: native-guardcert-versions native-variable-cancel-versions
native-guardcert-versions:
	python3 scripts/native_guardcert_versions.py
native-variable-cancel-versions:
	python3 scripts/native_variable_cancel_versions.py

.PHONY: native-affine-nest-affine-maps
native-affine-nest-affine-maps:
	python3 scripts/native_affine_nest_affine_maps.py
	python3 scripts/native_affine_nest_affine_maps_paths.py

.PHONY: native-affine-nest-composition
native-affine-nest-composition:
	python3 scripts/native_affine_nest_composition.py
	python3 scripts/native_affine_nest_composition_paths.py

.PHONY: native-affine-nest-accumulation
native-affine-nest-accumulation:
	python3 scripts/native_affine_nest_accumulation.py
	python3 scripts/native_affine_nest_accumulation_paths.py

.PHONY: native-affine-nest-accumulation-cost
native-affine-nest-accumulation-cost:
	python3 scripts/native_affine_nest_accumulation_cost.py
	python3 scripts/native_affine_nest_accumulation_cost.py --layout windows
