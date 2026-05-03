#!/usr/bin/env bash
#
# coq/Extracted/build.sh — compile the extracted Coq + driver into a
# standalone executable.
#
# Assumes:
# - The Rocq theory has already been built (`make -C coq`); the
#   Extraction.v compilation produced tzel_wots.ml + tzel_wots.mli in
#   coq/Impl/.
# - ocamlc is on PATH.
#
# We copy the extracted .ml/.mli into this directory and compile with
# plain ocamlc — no opam dependencies, no dune. Keeps the build
# minimal for the smoke-test pattern.

set -euo pipefail

DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
cd "$DIR"

src_ml="../Impl/tzel_wots.ml"
src_mli="../Impl/tzel_wots.mli"
[[ -f "$src_ml" && -f "$src_mli" ]] || {
  echo "missing extracted files: build the Rocq theory first" >&2
  echo "  (cd coq && rocq makefile -f _CoqProject -o Makefile && make -j2)" >&2
  exit 1
}

cp "$src_ml" "$src_mli" .

ocamlc -c tzel_wots.mli
ocamlc -c tzel_wots.ml
ocamlc -c main.ml
ocamlc -o chain_step tzel_wots.cmo main.cmo

echo "built: $DIR/chain_step"
