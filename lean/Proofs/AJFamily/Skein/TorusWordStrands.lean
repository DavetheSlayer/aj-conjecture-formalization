import Mathlib
import AJFamily.Skein.TorusWord

/-!
# The family word lives on `4k + 3` strands

`isOnStrands_whiteheadTorusWord`: every letter of `whiteheadTorusWord k` is a generator `σ_x` with
`x ≤ 4k + 1`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- Every letter of the band `b(i, j)` lies below `j`. -/
private theorem lt_of_mem_surfaceBand {i j : ℕ} {g : ℕ × Bool}
    (hg : g ∈ surfaceBand i j) : g.1 + 1 ≤ j ∨ g.1 = i := by
  simp only [surfaceBand, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hg
  rcases hg with (⟨x, hx, rfl⟩ | rfl) | ⟨x, hx, rfl⟩
  · left; dsimp only; omega
  · right; rfl
  · left; dsimp only; omega

theorem isOnStrands_whiteheadTorusWord (k : ℕ) :
    IsOnStrands (4 * k + 3) (whiteheadTorusWord k) := by
  intro g hg
  simp only [whiteheadTorusWord, List.mem_append, List.mem_singleton] at hg
  rcases hg with ((((((h | h) | h) | h) | h) | h) | h) | h
  · simp only [List.mem_map, List.mem_range] at h
    obtain ⟨l, hl, rfl⟩ := h
    simp only
    omega
  · have := lt_of_mem_surfaceBand h
    omega
  · have := lt_of_mem_surfaceBand h
    omega
  · rw [h]; simp only; omega
  · simp only [List.mem_flatMap, List.mem_range] at h
    obtain ⟨s, hs, h⟩ := h
    have := lt_of_mem_surfaceBand h
    omega
  · have := lt_of_mem_surfaceBand h
    omega
  · have := lt_of_mem_surfaceBand h
    omega
  · rw [h]; simp only; omega

end AJConjecture
