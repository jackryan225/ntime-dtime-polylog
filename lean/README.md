# The Lean 4 project

    sh scripts/get-upstream.sh   # fetch openai/math@3344da5 and ZIB-IOL/lemmata@a2dd430, apply the patches, check sha256
    lake exe cache get           # prebuilt Mathlib d13f23b
    lake build                   # builds Release.lean and its closure

What is where:
- `C1Challenge/`: the statement files. They import only Mathlib. Read these to know what is proved (`../LEAN-STATEMENT.md`).
- `Release.lean`: imports the four closed theorems, compares their types with the targets, prints their axioms.
- `P1*/`: our proof (746 files with the statement files).
- `OAI/`, `Lemmata/`: NOT in the repository; `scripts/get-upstream.sh` creates them (lists in `upstream/`).
- `patches/`: our two patches to OpenAI's files (`patches/README.md`).
- `CLOSURE-SHA256SUMS`: the sha256 of all 3,067 source files of the proof, as audited.
- `LICENSE`, `NOTICE`, `LICENSE-APACHE-2.0`: licenses.

The statement files end in `sorry` on purpose: each states its theorem as a target, and the proved theorem is a separate
declaration with the same type. Lake prints a `declaration uses 'sorry'` warning for the four targets; the proved theorems do
not depend on `sorryAx` (see the `#print axioms` lines of the build).

Names in comments. The comments of the proof files are working notes of the AI agents who wrote them: they name agent lanes
(for example `P1-lean-integ`), worker runs and file paths of the working repository in which the proof was written. Those paths
do not exist here. The comments were not edited, so that every file keeps the sha256 of the audit.
