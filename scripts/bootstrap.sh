#!/bin/sh
set -eu

guard_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
guard_opam_root=${GUARD_OPAM_ROOT:-"$guard_root/.toolchain/opam"}
guard_jobs=${GUARD_JOBS:-4}

if [ ! -f "$guard_opam_root/config" ]; then
  opam init --root="$guard_opam_root" --bare --disable-sandboxing --no-setup \
    --yes default https://opam.ocaml.org
fi
if [ ! -d "$guard_opam_root/guard/.opam-switch" ]; then
  opam switch create guard --root="$guard_opam_root" \
    ocaml-base-compiler.4.14.1 --yes --jobs="$guard_jobs"
fi
opam install --root="$guard_opam_root" --switch=guard \
  rocq-core.9.2.0 rocq-stdlib.9.2.0 menhir.20260209 --yes --jobs="$guard_jobs"
guard_ocaml_version=$(opam var --root="$guard_opam_root" --switch=guard ocaml:version)
if [ "$guard_ocaml_version" != 4.14.1 ]; then
  printf '%s\n' 'The selected switch must use OCaml 4.14.1.' >&2
  exit 1
fi
opam exec --root="$guard_opam_root" --switch=guard -- rocq --version
printf 'Run: opam exec --root=%s --switch=guard -- make check-compcert\n' "$guard_opam_root"
