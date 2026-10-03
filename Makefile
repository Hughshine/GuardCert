ROCQ ?= rocq
ROCQFLAGS ?=
SOURCES := theories/AbstractGuard.v theories/SemanticFacts.v theories/DomainRestriction.v theories/ResidualGuard.v \
           theories/AbstractSchedule.v theories/AbstractScheduleChecker.v theories/SchedulePermutation.v theories/EndpointBridge.v theories/BilateralTransport.v \
           theories/SilentRegionProtocol.v \
           theories/PolCertCompat.v \
           theories/GuardedRegion.v theories/CheckedGuard.v theories/Examples.v \
           theories/Presumption.v theories/Synthesis.v theories/ConditionalRewrite.v

.PHONY: all proof demo check fetch-compcert compcert-proof check-compcert compcert-bridge \
        guarded-compiler scheduled-compiler rectangular-compiler stripmine-compiler native-demo native-schedules native-rectangular native-stripmine check-integration polcert-proof polcert-affine-proof polcert-loop-proof \
        polcert-dynamic-proof polcert-nested-proof polcert-memory-proof \
        polcert-optimizer-proof polcert-store-native clean
all: check

proof:
	@mkdir -p build
	@$(ROCQ) --version > build/compiler.txt
	@set -eu; for src in $(SOURCES); do $(ROCQ) compile $(ROCQFLAGS) -Q theories Guard "$$src"; done

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
