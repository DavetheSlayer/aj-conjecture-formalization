import Mathlib
import AJHandoff.TorusKnot.PairKOrbOrder

/-!
# Sums along the two pieces of the orbit

A sum along the orbit indices `[iT, iH)` is the sum over the top block without `pairOrbH1`, and a
sum along `[0, iT) ∪ [iH + 1, m)` is the sum over the bottom block `[0, c - s] ∪ {2c}`
(`iT = pairOrbIdx r s T`, `iH = pairOrbIdx r s (pairOrbH1 r s)`).

Route: apply `pairOrb_sum_orbit` to `F` times the indicator of the region; by `pairOrb_top_iff`
and `pairOrbIdx_spec` the indicator along the orbit is the indicator of the index interval
(`Finset.sum_filter`, `Finset.sum_Ico_eq_sum_range`, `Finset.range_eq_Ico`,
`Finset.sum_Ico_consecutive`).
-/

namespace AJConjecture

/-- A sum along a set of orbit indices is the sum over the positions met there. -/
private theorem pairOrb_sum_of_iff {r s : ℕ} (h : IsTorusPair r s) (F : ℕ → ℤ)
    {S I : Finset ℕ} (hS : S ⊆ Finset.range (pairStrands r s))
    (hI : I ⊆ Finset.range (pairStrands r s))
    (hiff : ∀ k, k < pairStrands r s → (pairOrbT r s k ∈ S ↔ k ∈ I)) :
    ∑ k ∈ I, F (pairOrbT r s k) = ∑ t ∈ S, F t := by
  calc ∑ k ∈ I, F (pairOrbT r s k) =
      ∑ k ∈ Finset.range (pairStrands r s), if k ∈ I then F (pairOrbT r s k) else 0 := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hI]
    _ = ∑ k ∈ Finset.range (pairStrands r s),
        if pairOrbT r s k ∈ S then F (pairOrbT r s k) else 0 :=
      Finset.sum_congr rfl fun k hk ↦ by simp only [hiff k (Finset.mem_range.1 hk)]
    _ = ∑ t ∈ Finset.range (pairStrands r s), if t ∈ S then F t else 0 :=
      pairOrb_sum_orbit h fun t ↦ if t ∈ S then F t else 0
    _ = ∑ t ∈ S, F t := by rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hS]

/-- A sum along the top piece of the orbit. -/
theorem pairOrb_sum_top {r s : ℕ} (h : IsTorusPair r s) (F : ℕ → ℤ) :
    ∑ k ∈ Finset.Ico (pairOrbIdx r s (pairTop r s)) (pairOrbIdx r s (pairOrbH1 r s)),
        F (pairOrbT r s k) =
      ∑ t ∈ (Finset.Icc (pairC r s - s + 1) (pairTop r s)).erase (pairOrbH1 r s), F t := by
  obtain ⟨hT, hHt, -, -, -, -⟩ := pairOrbTop_basic h
  obtain ⟨-, -, hHm, -⟩ := pairOrb_idx_order h
  have hH := pairOrbIdx_spec h (show pairOrbH1 r s < pairStrands r s by
    unfold PairOrbTop pairTop pairStrands at *; omega)
  refine pairOrb_sum_of_iff h F ?_ ?_ fun k hk ↦ ?_
  · intro t ht
    rw [Finset.mem_erase, Finset.mem_Icc] at ht
    rw [Finset.mem_range]
    unfold pairTop pairStrands at *
    omega
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_range]
    omega
  · rw [Finset.mem_erase, Finset.mem_Icc, Finset.mem_Ico]
    have htop := pairOrb_top_iff h hk
    unfold PairOrbTop at htop
    have hne : pairOrbT r s k = pairOrbH1 r s ↔ k = pairOrbIdx r s (pairOrbH1 r s) := by
      constructor
      · intro he
        rw [← hH.2] at he
        exact pairOrbT_injOn h hk hH.1 he
      · rintro rfl
        exact hH.2
    rw [ne_eq, hne, htop]
    omega

/-- A sum along the two bottom pieces of the orbit. -/
theorem pairOrb_sum_bot {r s : ℕ} (h : IsTorusPair r s) (F : ℕ → ℤ) :
    ∑ k ∈ Finset.range (pairOrbIdx r s (pairTop r s)), F (pairOrbT r s k) +
        ∑ k ∈ Finset.Ico (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s),
          F (pairOrbT r s k) =
      ∑ t ∈ Finset.range (pairC r s - s + 1), F t + F (2 * pairC r s) := by
  obtain ⟨h0, h1, h2, h3⟩ := pairOrb_idx_order h
  have hc := pairOrb_arith h
  have hdisj : Disjoint (Finset.range (pairOrbIdx r s (pairTop r s)))
      (Finset.Ico (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Ico] at hk'
    omega
  have hnot : 2 * pairC r s ∉ Finset.range (pairC r s - s + 1) := by
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_union hdisj, add_comm (∑ t ∈ Finset.range (pairC r s - s + 1), F t),
    ← Finset.sum_insert hnot]
  refine pairOrb_sum_of_iff h F ?_ ?_ fun k hk ↦ ?_
  · intro t ht
    rw [Finset.mem_insert, Finset.mem_range] at ht
    rw [Finset.mem_range]
    unfold pairStrands
    omega
  · intro k hk
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico] at hk
    rw [Finset.mem_range]
    omega
  · rw [Finset.mem_insert, Finset.mem_range, Finset.mem_union, Finset.mem_range,
      Finset.mem_Ico]
    have htop := pairOrb_top_iff h hk
    have hlt := pairOrbT_lt h k
    have hTd : pairTop r s = 2 * pairC r s - 1 := rfl
    unfold PairOrbTop at htop
    unfold pairStrands at hlt
    constructor
    · intro hb
      have : ¬ (pairOrbIdx r s (pairTop r s) ≤ k ∧ k ≤ pairOrbIdx r s (pairOrbH1 r s)) := by
        rw [← htop]
        omega
      omega
    · intro hb
      have : ¬ (pairC r s - s + 1 ≤ pairOrbT r s k ∧ pairOrbT r s k ≤ pairTop r s) := by
        rw [htop]
        omega
      omega

end AJConjecture
