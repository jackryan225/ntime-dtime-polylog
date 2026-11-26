# Audit of the Lean proof

All times UTC. "Build machine": a Mac with 18 cores and 128 GB of memory, Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, openai/math `3344da59991ed94f9ba711217b29c1d760badfa6`. Logs: `logs/`
(the home folder and the machine name are replaced by `<home>` and `<host>`).

## 1. What is checked

| Theorem | Modules in its closure | `#print axioms` |
|---|---|---|
| `P1Final.c1_closed` | 3,037 (716 ours, 2,290 OpenAI, 31 Lemmata) | `propext`, `Classical.choice`, `Quot.sound` |
| `P1Final.c1_ntime_closed` | 3,048 | the same |
| `P1Final.c1u_closed` | 3,056 | the same |
| `P1Final.c1u_utime_closed` | 3,058 | the same |

Together: 3,066 source files, plus `C1Challenge/UTimeGuards.lean` (guards, in no closure) = the 3,067 files of
`lean/CLOSURE-SHA256SUMS`: 746 of ours, 2,290 of openai/math (6 of them changed by our two patches), 31 of ZIB-IOL/lemmata
(changed by openai/math's own patch). Each closed file compares the type of its theorem with the type of the target in the
Mathlib-only statement files as Lean terms (`run_meta`), and `lean/Release.lean` repeats the four comparisons.

## 2. Three kernels

1. **Lean's kernel**, during the build: every declaration of every module.
2. **leanchecker** (replays the compiled `.olean` files through the kernel again), 25 November: all 746 of our modules
   (412 + 304 modules of the closure of `c1_closed` in batches of 4, then the 11, 19, 2 and 1 modules added by the other
   theorems; 0 failures) and all 2,321 OpenAI and Lemmata modules (24 + 2,297 in a low-priority job that ended 23:06Z;
   0 failures).
3. **lean4lean** (an independent implementation of the Lean kernel, written in Lean) on the `lean4export` export of each
   theorem with its whole closure, Mathlib included (stack limit 65,520 KB, recursion depth 500,000):

| Theorem | Theorems in the export | Axioms in the export | lean4lean | Time |
|---|---|---|---|---|
| `c1_closed` | 64,224 | `Classical.choice`, `Quot.sound`, `propext` | checked 83,903 declarations, exit 0 | 137 s |
| `c1_ntime_closed` | 64,346 | the same | checked 84,109 declarations, exit 0 | 128 s |
| `c1u_closed` | 64,268 | the same | checked 84,016 declarations, exit 0 | 127 s |
| `c1u_utime_closed` | 64,279 | the same | checked 84,028 declarations, exit 0 | 135 s |

## 3. Clean rebuilds

- **25 November, 16:48Z** (audit): a fresh copy of the sources, an EMPTY build folder, Mathlib from a shared package folder:
  `lake build P1Final.Closed`, exit 0, "Build completed successfully (11960 jobs)", 3,287 s (other jobs ran on the machine
  at the same time). `#print axioms` there: standard axioms only.
- **26 November, 02:56Z to 03:23Z** (this project: every file of `lean/` is byte-identical to this repository, checked by
  sha256 after the build, except the text files `LICENSE`, `NOTICE`, `README.md`, `patches/README.md`, written later): a NEW
  folder; `scripts/get-upstream.sh`
  exit 0, all 3,067 files match `CLOSURE-SHA256SUMS`; an EMPTY build folder, Mathlib from a shared package folder at
  `d13f23b`; `LEAN_NUM_THREADS=8 lake build`: exit 0, "Build completed successfully (11992 jobs)", 3,068 modules built in this
  run (every `.olean`; no artifact cache), **1,611 s** wall clock (7,198 s user CPU). Memory: peak resident set of one process
  22.5 GB (24.3 GB by `/usr/bin/time -l`); summed over the build's process tree 53.5 GB at the peak (11 processes; mapped
  library files are counted once per process, so the true total is lower). Build folder: 11 GB. The log has the eight lines
  "has exactly the type of" (four from the closed files, four from `Release.lean`) and `[propext, Classical.choice, Quot.sound]`
  for each of the four theorems; `lake env lean Release.lean` repeats them (exit 0). The only "declaration uses `sorry`"
  warnings are the four targets in `C1Challenge/{Statement,NTime,C1U,UTime}.lean`. After the build all 3,067 files still match.
- Sources of that test: the 2,290 OpenAI files came from a clean checkout of openai/math at `3344da5`. No copy of
  ZIB-IOL/lemmata at `a2dd430` was at hand, so the 31 audited Lemmata files with the hunks of OpenAI's lemmata patch reversed
  served as the upstream input. The test therefore covers the copy, patch and sha256 steps and the build. It does not cover the
  two `git clone` commands, and it does not show that the upstream Lemmata files equal that reconstruction (if they differ,
  the sha256 step of the script stops).

## 4. Source scan

Patterns: `sorry`, `admit`, `native_decide`, `ofReduceBool`, `trustCompiler`, `axiom` declarations, `implemented_by`,
`extern`, over all 3,068 source files of the release build (job of 26 November): 733 hits, all harmless.
- 16 `sorry`: 4 are the target placeholders of the four statement files (`Statement.lean:126`, `NTime.lean:94`, `C1U.lean:75`,
  `UTime.lean:24`; not used, see the axioms); 12 are in comments ("no `sorry`", "sorry-free").
- 32 `admit`: OpenAI's functions `MotifAdmission.admit` and `Replay.admit`, our uses of them, and the English word.
- 685 `extern`: the word "external" in comments and names. No `@[extern]`, no `implemented_by`.
- 0 `native_decide`, 0 `ofReduceBool`, 0 `trustCompiler`, 0 `axiom` declarations.
The audit scan of 25 November (closure of `c1_closed`, 3,037 files) gave the same picture (`logs/audit-2026-11-25/c1-clean-scan2.txt`).

## 5. Checksums

- `lean/CLOSURE-SHA256SUMS`: the sha256 of all 3,067 source files. It is the audit list of 25 November (the closure of
  `c1_closed` and the addenda for the other three theorems), with no change. `scripts/get-upstream.sh` checks every fetched
  and patched file against it.
- Build inputs, the same as in the audit: `lean-toolchain` `d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b`
  (leanprover/lean4:v4.34.1), `lake-manifest.json` `77f95c19ff09a8e80206015803a7512337532fe82dd02d36ce27b1c817ce8e92`,
  `patches/field-uniform.patch` `32a3d814c7bd3fb45f528979da619d594cf5baaec9143d9fdb0637c00405021f`,
  `patches/port-over.patch` `5efa498961c36d2da7f4b6d80ee0af7d2a7a4609c04c969f932c75052f5a330a`.
- Changed for the release: `lakefile.toml` (only the libraries of the closure, and the default target `Release`; the
  options are the same: `autoImplicit = false`, nothing else) and the new file `Release.lean` (imports, the four type
  comparisons, `#print axioms`). Neither adds a declaration to the proof.
- `SHA256SUMS` (top folder): every file of this repository except itself.

## 6. Limits of the audit

- The kernels check the proof of the statement as written in `lean/C1Challenge/`. Whether those definitions mean what the
  paper means is a question of reading; see `LEAN-STATEMENT.md`. No human has read them.
- The equivalence of the Lean machine model with the paper's model is argued in words, not in Lean.
- The proof was written in one day by AI agents (about ten statements of the plan were found false on the way and repaired;
  none of them was the statement of a theorem above after its file was fixed). The kernels make the proof independent of
  how it was written; they do not make the statement right.
- The fetch step of `scripts/get-upstream.sh` (the two `git clone` commands) was not run in our test (section 3); the files
  it must produce are pinned by sha256.
- Logs: `logs/audit-2026-11-25/` (clean rebuild, leanchecker, export, lean4lean, axioms) and `logs/release-build-2026-11-26/`
  (`job.log` is the summary; `build.txt` the full build output).
