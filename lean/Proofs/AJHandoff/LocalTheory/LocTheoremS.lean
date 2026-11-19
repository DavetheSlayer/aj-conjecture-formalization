import Mathlib
import AJHandoff.LocalTheory.LocSeqGerm

/-!
# I-SEQ: Theorem S over `K = ℚ(t, M)`

**Theorem S.** Let `P ∈ K[L; τ]` be irreducible of positive degree (an operator of positive
Laurent span is `L^j` times such a `P` with nonzero constant coefficient; the constant
coefficient is not needed), and let `F` be a tail sequence not in the embedded copy of `K`
with `P F = r ∈ K` (`r` may be `0`). Then every `G ∈ K[L; τ]` with `G F = 0` is a left multiple
`H ⋆ P`; in particular `P` right-divides every annihilator of the selected `F`. Neither `r ≠ 0`
nor `P F = 0` is assumed. Instance of `exists_eq_oreMul_of_diffAct_eq_zero` with `E` the germs of
sequences and `W = ev(K)`.

The constant sequence shows that nonrationality is essential: for `F = 1` and any irreducible
`P` of positive order, `P F = P(1) ∈ K` while `L - 1` annihilates `F` (see `LocConstantControl`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- **Theorem S** with forcing in `K`, including `0`. -/
theorem seq_theoremS {P : SeqField[X]} (hP : OreIrreducible seqShift P) {F : SeqGerm}
    (hF : F ∉ seqEval.range)
    (hPF : diffAct seqEval seqGermShift P F ∈ seqEval.range) {G : SeqField[X]}
    (hG : diffAct seqEval seqGermShift G F = 0) : ∃ H : SeqField[X], G = oreMul seqShift H P :=
  exists_eq_oreMul_of_diffAct_eq_zero seqShift seqEval seqGermShift seqGermShift_seqEval
    seqEval.range.toAddSubgroup
    (fun a _ ⟨x, hx⟩ ↦ ⟨a * x, by rw [map_mul, hx]⟩)
    (fun _ ⟨x, hx⟩ ↦ ⟨seqShift x, by rw [← seqGermShift_seqEval, hx]⟩) hP hF hPF hG

end AJConjecture
