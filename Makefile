# All lake invocations are wrapped in `nix-shell --run` so the native
# crypto libraries (libsodium, libsecp256k1, libblst) required by
# Cryptograph.FFI's extern_lib targets are on the compiler/linker path.
#
# Override NIX_RUN= (empty) to skip the wrapper if you're already inside
# a shell that has those libraries, e.g.
#     make NIX_RUN= build_all
NIX_RUN ?= nix-shell --run

.PHONY: usage
usage:
	@echo "usage: make <command>"
	@echo "Available commands:"
# Dev shell
	@echo " - shell:              Enter the nix-shell with libsodium, libsecp256k1, libblst."
# Plutus Core
	@echo " - build_plutus_core:  Build PlutusCore formalization."
	@echo " - clean_plutus_core:  Clean compiled lean files for PlutusCore formalization."
	@echo " - check_plutus_core:  Same as build_plutus_core but also checks that each lean file"
	@echo "                       in the PlutusCore formalization is considered during compilation."
# Cryptograph
	@echo " - build_cryptograph:  Build pure-Lean Cryptograph library."
	@echo " - clean_cryptograph:  Clean compiled lean files for Cryptograph."
	@echo " - check_cryptograph:  Same as build_cryptograph but also checks that each lean file"
	@echo "                       in Cryptograph is considered during compilation."
# Cryptograph FFI
	@echo " - build_ffi:          Build Cryptograph.FFI Lean modules + all four native extern_libs."
	@echo " - clean_ffi:          Clean compiled lean files (shared with other targets)."
# Conformance test generator
	@echo " - gen_conformance_tests: (Re)generate the conformance test suite under"
	@echo "                          Tests/Conformance/Generated/ from CONFORMANCE_ROOT"
	@echo "                          (default: .plutus-conformance/plutus-conformance)."
	@echo "                          Pass excludeNotImplemented=1 to skip test"
	@echo "                          categories whose features are not yet"
	@echo "                          implemented in this Lean formalization."
	@echo " - build_conformance:  Build the conformance test suite (Tests.Conformance)."
	@echo " - check_conformance:  Same as build_conformance but also checks that each"
	@echo "                       lean file under Tests/Conformance/ is considered"
	@echo "                       during compilation. Requires .plutus-conformance"
	@echo "                       symlink and a previously generated test suite."
# Test suite
	@echo " - build_tests:        Build Test suite."
	@echo " - clean_tests:        Clean compiled lean files for the Test suite."
	@echo " - check_tests:        Same as build_tests but also checks that each lean file"
	@echo "                       in the Test suite is considered during compilation."
# Aggregates
	@echo " - build_all:          Build PlutusCore, Cryptograph, FFI, and Tests."
	@echo " - clean_all:          Clean everything."
	@echo " - check_all:          Run every check_* target."

# ------------------------------------------------------------------ #
# Dev shell                                                          #
# ------------------------------------------------------------------ #

.PHONY: shell
shell:
	nix-shell

# ------------------------------------------------------------------ #
# PlutusCore                                                         #
# ------------------------------------------------------------------ #

.PHONY: build_plutus_core
build_plutus_core:
	$(NIX_RUN) 'lake build PlutusCore && lake build Lemmas'

.PHONY: clean_plutus_core
clean_plutus_core:
	$(NIX_RUN) 'lake clean'

.PHONY: check_plutus_core
check_plutus_core: clean_plutus_core
	$(NIX_RUN) './scripts/check_lean_project_with_lemmas.sh PlutusCore'

# ------------------------------------------------------------------ #
# Cryptograph (pure Lean)                                            #
# ------------------------------------------------------------------ #

.PHONY: build_cryptograph
build_cryptograph:
	$(NIX_RUN) 'lake build Cryptograph'

.PHONY: clean_cryptograph
clean_cryptograph:
	$(NIX_RUN) 'lake clean'

.PHONY: check_cryptograph
check_cryptograph: clean_cryptograph
	$(NIX_RUN) './scripts/check_lean_project_compilation.sh Cryptograph'

# ------------------------------------------------------------------ #
# Cryptograph.FFI (Lean externs + C shims)                           #
# ------------------------------------------------------------------ #

.PHONY: build_ffi
build_ffi:
	$(NIX_RUN) 'lake build Cryptograph.FFI \
	            leanPlutusHash leanPlutusEd25519 \
	            leanPlutusSecp256k1 leanPlutusBls12_381'

.PHONY: clean_ffi
clean_ffi:
	$(NIX_RUN) 'lake clean'

# ------------------------------------------------------------------ #
# Test suite                                                         #
# ------------------------------------------------------------------ #

.PHONY: build_tests
build_tests:
	$(NIX_RUN) 'LEAN_NUM_THREADS=5 lake test'

.PHONY: clean_tests
clean_tests:
	$(NIX_RUN) 'lake clean'

.PHONY: check_tests
check_tests: clean_tests
	$(NIX_RUN) 'LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests Tests Tests/Conformance'

# Path to the plutus-conformance directory containing test-cases/.
CONFORMANCE_ROOT ?= .plutus-conformance/plutus-conformance
# Path string embedded in generated #import_uplc lines (interpreted at test-build time).
CONFORMANCE_EMBED_ROOT ?= .plutus-conformance/plutus-conformance

# Optional: set excludeNotImplemented=1 (or any non-empty value) to skip test
# categories whose underlying features are not yet implemented in this Lean
# formalization.
ifneq ($(strip $(excludeNotImplemented)),)
EXCLUDE_NOT_IMPLEMENTED_FLAG := --exclude-not-implemented
else
EXCLUDE_NOT_IMPLEMENTED_FLAG :=
endif

.PHONY: gen_conformance_tests
gen_conformance_tests:
	lake build gen_conformance_tests
	lake exe gen_conformance_tests $(CONFORMANCE_ROOT) \
		--out Tests/Conformance/Generated \
		--embed-root $(CONFORMANCE_EMBED_ROOT) \
		$(EXCLUDE_NOT_IMPLEMENTED_FLAG)

.PHONY: build_conformance
build_conformance:
	$(NIX_RUN) 'LEAN_NUM_THREADS=5 lake build Tests.Conformance'

.PHONY: check_conformance
check_conformance: clean_tests
	$(NIX_RUN) 'LEAN_NUM_THREADS=5 ./scripts/check_lean_project_compilation.sh Tests.Conformance Tests/Conformance'

# ------------------------------------------------------------------ #
# Aggregates                                                         #
# To maintain when you add new components                            #
# ------------------------------------------------------------------ #

.PHONY: build_all
build_all: build_plutus_core build_cryptograph build_ffi build_tests

.PHONY: clean_all
clean_all: clean_plutus_core clean_cryptograph clean_ffi clean_tests

.PHONY: check_all
check_all: check_plutus_core check_cryptograph check_tests
