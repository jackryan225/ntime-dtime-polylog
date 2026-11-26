import P1Final.OneOpen
import P1Int.PortData

/-!
# P1Final.Main: `C1Challenge.c1` from the ONE open Prop (owner: P1-lean-integ; DRAFT of the final file)

State of 2026-11-25, 11:40Z. Proved and linked in this project: Case 1 (`c1_of_priceTwo_final`), W2
(`w2_closed`), W3 (`w3_closed`), the count and the dispatcher (lane count), the P11 glue
(`P1Int.P11.lemmaP_of_countHyp`), the network glue (`P1Int.P11.countInput_of_net`), the port data
(`P1Int.P11.portData_of_portTwo`).

The ONE open input is `P1Int.P11.OpenP11`: for the data of every port (schedule `S`, templates `Bt`, a finite
`F_2`-algebra `F` with a solution `κ`, a basis `bs`, a functional `l` with `l 1 = 1`) there is a dyadic exponent
`j` such that `P1Int.P11.NetHyp Bt κ hκ bs l (2^-j)` holds. Its named parts, per two-constant parity verifier
`(L, V, a, b, n₀)` with `1 ≤ b` and per input `x` of length at least `n₁` (see `P1Int.P11.NetHyp`, `NetInput`):

| part | text in `NetHyp` / `NetInput` | owner |
|---|---|---|
| alphabet, `bit`, `letter`, `answer`, check programs `chk` | `∃ A _ bit letter _ _ answer _ chk c n₁` | checks + Sol dispatch (Task → Prog) |
| selector length | `4 ≤ lpK2 a b |x|` | integ (arithmetic, from `n₁`) |
| dispatcher budget | `∃ bnd, 1 ≤ bnd ∧ 16 + bnd ≤ lpCost2 c s a b |x|` | Sol dispatch (`cost_le`) |
| totality of every check program | `∀ u c' Rc ρ, ∃ v, ProgAnswers Rc .. v bnd` | checks (programs) |
| parameters | `∃ Bk _ I _ h Tc (hn : Tc * S.laneBits ≤ h)` | P10: `P1Wrap.Params`, `lane_bound`, `neZero_B`, `neZero_I` |
| run bound | `lpTime a b |x| ≤ I * 2 ^ h * Bk` | `P1Int.P11.run_bound` (PROVED for `Params`) |
| routed network count | `∀ σ, P1Net.ContractEqCount ..` | net + P1-astra-contract (OPEN) |
| final site order | `ord` | Sol witfill (D9: `y * lanes + l`) |
| witness code | `enc`, `Function.Injective enc` | P6 (proved) + Sol witfill (`encTuple_injective`) |
| checks | `hchecks` (all check programs accept `u` iff `u` encodes a valid tuple) | chkdir, chkfinal, P5, Sol provers |

FINAL STEP (one job, see research/p1/lean/Final/AUDIT.md): when `theorem P1Final.openP11 : P1Int.P11.OpenP11` exists,
rename `C1.lean.draft` to `C1.lean` and `C1Check.lean.draft` to `C1Check.lean` and run the audit.
-/

namespace P1Final

/-- **C1 from the one open Prop.** -/
theorem c1_of_openP11 (p11 : P1Int.P11.OpenP11) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ L : List Bool → Bool,
      C1Challenge.NTIMELinLog L ∧ ¬ C1Challenge.DTIMEIn L (fun n => (n : ℝ) * Real.logb 2 n ^ σ) :=
  c1_of_countHyp (P1Int.P11.countHyp_of_portTwo p11)

end P1Final
