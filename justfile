# SPDX-License-Identifier: Apache-2.0
# One-word task runner for promislow-fracton-amoeba (Build Standard v1.2.0 A31)

set shell := ["bash", "-cu"]

default:
  @just --list

demo:
  PYTHONPATH=python python examples/quickstart_demo.py

rust:
  cd rust && cargo test --release && cargo run --release -- summary

python:
  PYTHONPATH=python python python/pfa_verify/exact_core.py

test:
  PYTHONPATH=python pytest tests/test_all.py -v

mutate:
  PYTHONPATH=python python scripts/mutate.py

figures:
  PYTHONPATH=python python scripts/make_figures.py

lean:
  cd lean && lake build && lake env lean VerifyAxioms.lean

kernels:
  cd lean && lake env leanchecker Solution && lake env leanchecker PalomarSolution && lake comparator --config comparator.json --paranoid

paper:
  cd paper && tectonic -X compile main.tex --outdir build --keep-logs --keep-intermediates

citations:
  python scripts/check_citations.py

audit:
  python scripts/check_readme_axioms.py
  python scripts/audit_repo.py

all: rust python test mutate lean paper audit
