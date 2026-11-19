import Mathlib
import AJHandoff.TorusKnot.PairKCommutant
import AJHandoff.TorusKnot.PairKSatellite
import AJHandoff.TorusKnot.PairKTorusGroup

/-!
# The `SL₂(ℂ)` dichotomy for the torus companion, both central signs

`companionDichotomy_torusPairKnot`: for every representation `ρ` of the group of `T(r, s)` into
`SL₂(ℂ)`, `ρ(λ) = 1` or `ρ(λ) = z ρ(μ)^(-rs)` with `z` central. Route: `z := ρ(Π^s)` commutes
with every `ρ(x_j)` (`torusFullProd_pow_comm`). If `z` is scalar it is central and
`ρ(λ) = z ρ(μ)^(-rs)` (`longitude_torusPairKnot`); this covers `ε = +1` and `ε = -1` for
`r ≥ 3` and reducible nonabelian images. Otherwise the `ρ(x_j)` pairwise commute
(`commute_of_commute_nonscalar`), so the image is abelian, the conjugate generators have equal
images (`exists_conj_meridian`), `ρ(Π) = ρ(μ)^r` and `ρ(λ) = 1`.
-/

namespace AJConjecture

/-- T-CLASS (companion): the dichotomy for `T(r, s)` with exponent `m = rs`. -/
theorem companionDichotomy_torusPairKnot {r s : ℕ} (h : IsTorusPair r s) :
    CompanionDichotomy (torusPairKnot r s h) (r * s) := by
  intro ρ
  set z := ρ (torusFullProd h ^ s) with hz
  have hzc : ∀ x, Commute (z : Matrix (Fin 2) (Fin 2) ℂ) (ρ x : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro x
    have h1 := congrArg ρ (torusFullProd_pow_comm h x)
    rw [map_mul, map_mul] at h1
    exact congrArg Subtype.val h1
  by_cases hsc : ∃ a : ℂ, (z : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.scalar (Fin 2) a
  · right
    obtain ⟨a, ha⟩ := hsc
    refine ⟨z, fun x ↦ Subtype.ext ?_, ?_⟩
    · simp only [Matrix.SpecialLinearGroup.coe_mul, ha]
      exact Matrix.scalar_commute a (fun r' ↦ Commute.all a r') _
    · rw [longitude_torusPairKnot, map_mul, map_zpow]
  · left
    push Not at hsc
    have hcomm : ∀ i j : Fin (torusPairKnot r s h).strands,
        Commute (ρ (PresentedGroup.of i)) (ρ (PresentedGroup.of j)) := by
      intro i j
      have := commute_of_commute_nonscalar hsc (hzc (PresentedGroup.of i))
        (hzc (PresentedGroup.of j))
      exact Subtype.ext this.eq
    have hcen : ∀ x, Commute (ρ (meridian (torusPairKnot r s h))) (ρ x) := by
      intro x
      have hmem : x ∈ (Subgroup.centralizer {ρ (meridian (torusPairKnot r s h))}).comap ρ := by
        refine PresentedGroup.generated_by _ _ (fun j ↦ ?_) x
        rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact (hcomm _ j).eq
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hmem
      exact hmem _ rfl
    have hgen : ∀ j : Fin (torusPairKnot r s h).strands,
        ρ (PresentedGroup.of j) = ρ (meridian (torusPairKnot r s h)) := by
      intro j
      obtain ⟨g, hg⟩ := exists_conj_meridian (torusPairKnot r s h) j
      rw [hg, map_mul, map_mul, map_inv, ← (hcen g).eq]
      group
    have hP : ρ (torusFullProd h) = ρ (meridian (torusPairKnot r s h)) ^ r := by
      have key : ∀ l : List (Fin (torusPairKnot r s h).strands), (l.map fun j ↦
          ρ (PresentedGroup.of j : KnotGroup (torusPairKnot r s h))).prod =
          ρ (meridian (torusPairKnot r s h)) ^ l.length := by
        intro l
        induction l with
        | nil => simp
        | cons j l ih =>
          rw [List.map_cons, List.prod_cons, ih, hgen j, List.length_cons, pow_succ']
      rw [torusFullProd, map_list_prod]
      refine Eq.trans ?_ ((key (List.finRange r)).trans
        (congrArg (ρ (meridian (torusPairKnot r s h)) ^ ·) (List.length_finRange (n := r))))
      exact congrArg List.prod List.map_map
    rw [longitude_torusPairKnot, map_mul, map_zpow, map_pow, hP, ← pow_mul, zpow_neg,
      zpow_natCast, mul_inv_cancel]

end AJConjecture
