import P1ChkFinal.Progs

namespace P1SolFmt

open OAI.Computability.IntegerMultiplication Code P1Wit

namespace SolFormat

private theorem poly_cons {X : Type} [Codec X] {f : X → List Bool}
    {g : X → List (List Bool)} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x :: g x) := (hf.pair hg).compose Poly.cons

/-- Assemble the twelve format words from their polynomial-time components. -/
theorem format_words_poly_of (d : List Bool → Dims)
    (hfin : Poly (fun w : List Bool => Nat.bits (P1ChkFinal.finN (d w))))
    (harcs : Poly (fun w : List Bool => Nat.bits (P1ChkFinal.finArcs (d w))))
    (hslots : Poly (fun w : List Bool => Nat.bits ((d w).lv (d w).top).slots))
    (hlanes : Poly (fun w : List Bool => Nat.bits ((d w).lv (d w).top).lanes))
    (hOmegaOff : Poly (fun w : List Bool => Nat.bits ((d w).off (d w).secOmega)))
    (hOmegaWidth : Poly (fun w : List Bool => Nat.bits ((d w).width (d w).secOmega)))
    (hWidthOff : Poly (fun w : List Bool =>
      Nat.bits ((d w).off (secLev (d w).top .width))))
    (hWidthWidth : Poly (fun w : List Bool =>
      Nat.bits ((d w).width (secLev (d w).top .width))))
    (hChainOff : Poly (fun w : List Bool => Nat.bits ((d w).off (d w).secChain)))
    (hChainWidth : Poly (fun w : List Bool => Nat.bits ((d w).width (d w).secChain)))
    (hfixed : Poly (fun w : List Bool => Nat.bits (d w).fixedLen))
    (hchain : Poly (fun w : List Bool => Nat.bits (d w).chainLen)) :
    Poly (fun w => P1ChkFinal.fmt (d w)) := by
  exact poly_cons hfin (poly_cons harcs (poly_cons hslots (poly_cons hlanes
    (poly_cons hOmegaOff (poly_cons hOmegaWidth (poly_cons hWidthOff (poly_cons hWidthWidth
      (poly_cons hChainOff (poly_cons hChainWidth (poly_cons hfixed
        (poly_cons hchain (Code.Poly.const ([] : List (List Bool))))))))))))))

end SolFormat

/-- Assemble the twelve format words from their polynomial-time components. -/
theorem fmt_poly_of (dims : ℕ → Dims)
    (hfin : Poly (fun w : List Bool => Nat.bits (P1ChkFinal.finN (dims (P1Batch.bval w)))))
    (harcs : Poly (fun w : List Bool => Nat.bits (P1ChkFinal.finArcs (dims (P1Batch.bval w)))))
    (hslots : Poly (fun w : List Bool => let d := dims (P1Batch.bval w); Nat.bits (d.lv d.top).slots))
    (hlanes : Poly (fun w : List Bool => let d := dims (P1Batch.bval w); Nat.bits (d.lv d.top).lanes))
    (hOmegaOff : Poly (fun w : List Bool => let d := dims (P1Batch.bval w); Nat.bits (d.off d.secOmega)))
    (hOmegaWidth : Poly (fun w : List Bool => let d := dims (P1Batch.bval w); Nat.bits (d.width d.secOmega)))
    (hWidthOff : Poly (fun w : List Bool =>
      let d := dims (P1Batch.bval w); Nat.bits (d.off (secLev d.top .width))))
    (hWidthWidth : Poly (fun w : List Bool =>
      let d := dims (P1Batch.bval w); Nat.bits (d.width (secLev d.top .width))))
    (hChainOff : Poly (fun w : List Bool => let d := dims (P1Batch.bval w); Nat.bits (d.off d.secChain)))
    (hChainWidth : Poly (fun w : List Bool => let d := dims (P1Batch.bval w); Nat.bits (d.width d.secChain)))
    (hfixed : Poly (fun w : List Bool => Nat.bits (dims (P1Batch.bval w)).fixedLen))
    (hchain : Poly (fun w : List Bool => Nat.bits (dims (P1Batch.bval w)).chainLen)) :
    P1ChkFinal.FmtHyp dims := by
  exact SolFormat.format_words_poly_of (fun w => dims (P1Batch.bval w))
    hfin harcs hslots hlanes hOmegaOff hOmegaWidth hWidthOff hWidthWidth
    hChainOff hChainWidth hfixed hchain

end P1SolFmt
