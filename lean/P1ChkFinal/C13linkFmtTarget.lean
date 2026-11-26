import P1ChkFinal.ProgSolFmt
import P1ChkFinal.ProgC13link

/-!
# P1ChkFinal.C13linkFmtTarget: the C13link program with ONLY the format input (statement; lane P1-lean-greedy)

`progC13link` (ProgC13link.lean) still has the inputs `hM` (fit for EVERY n: false for short inputs in general), `hrq`, `hdec`,
`hfb` (nobody proved them; eval's `cone_c13link_task` passes them on). As Sol finalprog did for C13ends (`progC13ends_fmt`,
ProgSolFmt.lean), the target below keeps only `BatchHyp`, `LenHyp`, `FmtHyp dims` and the cone program `WHyp`;
`FmtHyp` is PROVED at the genuine dims (`P1SolFmt.SolFormat.fmtHyp_genuine`).
-/

namespace P1ChkFinal

open OAI.Computability.IntegerMultiplication OAI.Computability.IntegerMultiplication.Code P1Wit Module
open scoped Classical

/-- **Target of Sol P1-sol-c13lfmt** (statement only). -/
def C13linkFmtTarget : Prop :=
  ∀ {F : Type} [CommRing F] [Algebra (ZMod 2) F] {Dd : ℕ} (b : Basis (Fin Dd) (ZMod 2) F) (dims : ℕ → Dims)
    (Wof : List Bool → List Bool → ℕ → F) (M K : ℕ → ℕ) (βW : QDom M K → ℕ),
    BatchHyp → LenHyp → FmtHyp dims → WHyp b Wof M K βW →
    ∃ c : ℕ, Code.Task (fun p : QDom M K => budget c p.val + βW p) (fun p => send p.val)
      (fun p => send (decide (C13linkw b dims Wof p.val.1 p.val.2.1 (P1Batch.bval p.val.2.2))))

end P1ChkFinal
