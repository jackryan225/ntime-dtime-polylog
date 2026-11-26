import P1Final.Closed
import P1Int.Assembly
import P1Int.P11Count
import P1Int.PortData

/-!
# P1Final.LemmaPClosed: Lemma P in the port case, closed (P1-lean-integ, 2026-11-25; C1U-NOTE item 3/7)

Input T3 of the C1-U brief (ORG/briefs/PNP-c1u-lean.md): `P1Int.LemmaPOfPort PortTwo` from the two closed inputs of the
C1 chain (`P1Final.netP4`, `P1Final.openChecksRec_closed`).
-/

open OAI.Computability.MultitapeWeakETH (PortTwo)

theorem P1Final.lemmaP_port_closed : P1Int.LemmaPOfPort PortTwo :=
  P1Int.P11.lemmaP_of_portTwo_of_countHyp
    (P1Int.P11.countHyp_of_portTwo
      (P1Int.P11.openP11_of_parts P1Final.netP4 (P1Int.P11.openChecks_of_rec P1Final.openChecksRec_closed)))

example : P1Int.LemmaPOfPort OAI.Computability.MultitapeWeakETH.PortTwo := P1Final.lemmaP_port_closed

#print axioms P1Final.lemmaP_port_closed
