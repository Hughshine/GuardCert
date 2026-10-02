ROCQ ?= rocq
ROCQFLAGS ?=
SOURCES := theories/GuardedRegion.v theories/CheckedGuard.v theories/Examples.v \
           theories/Presumption.v theories/Synthesis.v theories/ConditionalRewrite.v

.PHONY: all proof demo check fetch-compcert compcert-proof check-compcert compcert-bridge \
        guarded-compiler native-demo check-integration clean
all: check

proof:
	@mkdir -p build
	@$(ROCQ) --version > build/compiler.txt
	@set -eu; for src in $(SOURCES); do $(ROCQ) compile $(ROCQFLAGS) -Q theories Guard "$$src"; done

demo:
	python3 prototype/demo.py
	python3 prototype/synthesis_demo.py

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

BRIDGE_SOURCES := theories/CompCertArithmetic.v theories/ClightGuard.v \
                  theories/ClightGuardProof.v theories/ClightEncodedRule.v theories/ClightNoWrap.v \
                  theories/ClightExprRewrite.v theories/ClightExprRewriteProof.v \
                  theories/ClightExprRule.v theories/CommonRewrites.v \
                  theories/CompCertMemoryRule.v \
                  theories/GuardCompiler.v theories/ClightIntegrationExamples.v \
                  theories/CommonRewriteExamples.v

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

guarded-compiler: check-compcert
	@python3 scripts/build_compiler.py > build/native-build.log 2>&1 || \
	  { cat build/native-build.log; exit 1; }

native-demo: guarded-compiler
	python3 scripts/native_demo.py
	python3 scripts/native_rewrites.py

check-integration: native-demo

clean:
	@python3 scripts/clean.py
