import Mathlib
import AJHandoff.TorusKnot.PairKKnot
import AJHandoff.TorusKnot.PairKSatellite
import AJHandoff.TorusKnot.PairKTorusGroup
import AJHandoff.TorusKnot.PairKPeriOrbit
import AJFamily.Classical.FamilyPeripheralLongitude

/-!
# The satellite structure of the knot group of `Wh⁻₀(T(r, s))` (crux)

`isWhSatellite_pairWhiteheadKnot`: the knot group of `pairWhiteheadKnot r s h` is a Whitehead
satellite of the group of `T(r, s)`. This is the analogue of
`satellitePeripheral_whiteheadTorusKnot` (`AJFamily.Classical.FamilyPeripheral*`, 2.6k lines
for `r = 2`), by the same chamber-product method, which is general for block lists
(`gapProd_fixed`, `edgeMer_fixed`, `map_longitude_blocks`). The proof assembles:

1. the gap relations of `pairBlocks r s` (`pairGapRels_of_hom`);
2. the companion tuple `z`, the half twist of the rotated staircase window, fixed by
   `(σ_0 ⋯ σ_(r-2))^s` (`pairCompTuple_fixed`), which gives `φ` by `PresentedGroup.toGroup`;
3. the Hopf loops `H₁ = R_0 β⁻¹ α`, `H₂ = C H₁ α⁻¹ H₁⁻¹ β R_0⁻¹` (`pairHopf_loops`), which with
   the gap relations `C R_0 = 1`, `H₂ H₁ = 1` give the clasp `R_0 = α β⁻¹ α⁻¹ β`;
4. the orbit loop `λ = G H₁⁻¹ M H₁ U` with `μ = G β G⁻¹`, `α = U μ U⁻¹`, `U⁻¹ R_0 U = z_0`,
   `G U = Λ` and `G R_0⁻¹ M R_0 G⁻¹ = Λ⁻¹` (`pairOrbit_split`);

and the pure group theory of `pairWh_algebra` (the last step of
`isSatelliteData_of_famRelations` in the case `r = 2`).
-/

namespace AJConjecture

/-- The braid relations hold for a tuple fixed by the braid. -/
private theorem lift_artinRels_of_fixed_peri {G : Type*} [Group G] (K : BraidKnot)
    (f : Fin K.strands → G) (hf : (braidRun K.strands K.word f).1 = f) :
    ∀ x ∈ artinRels K, FreeGroup.lift f x = 1 := by
  rintro _ ⟨k, rfl⟩
  rw [map_mul, map_inv, FreeGroup.lift_apply_of, map_mul, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one, lift_artinWord_snd, ← braidRun_fst_apply, hf]

/-- The clasp: the two Hopf loops and the relations `C R = 1`, `H₂ H₁ = 1` give
`R = α β⁻¹ α⁻¹ β`. -/
private theorem pairWh_clasp {G : Type*} [Group G] (R C h₁ h₂ α β : G) (hC : C * R = 1)
    (htop : h₂ * h₁ = 1) (hH1 : h₁ = R * β⁻¹ * α)
    (hH2 : h₂ = C * h₁ * α⁻¹ * h₁⁻¹ * β * R⁻¹) : R = α * β⁻¹ * α⁻¹ * β := by
  have hC' : C = R⁻¹ := eq_inv_of_mul_eq_one_left hC
  subst hC' hH1 hH2
  have h1 : R⁻¹ * (R * β⁻¹ * α) * α⁻¹ * (R * β⁻¹ * α)⁻¹ * β * R⁻¹ * (R * β⁻¹ * α) =
      β⁻¹ * α⁻¹ * β * R⁻¹ * β * β⁻¹ * α := by group
  rw [h1] at htop
  have h2 : R⁻¹ = (β⁻¹ * α⁻¹ * β)⁻¹ * (β⁻¹ * α⁻¹ * β * R⁻¹ * β * β⁻¹ * α) * α⁻¹ := by group
  rw [htop, mul_one] at h2
  rw [← inv_inv R, h2]
  group

/-- The pure group theory of the assembly: the companion meridian and the pattern longitude
from the clasp, the Hopf loop and the three orbit identities. -/
private theorem pairWh_algebra {G : Type*} [Group G] (μ α β h R Gg M U z₀ Λ l : G)
    (hl : l = Gg * h⁻¹ * M * h * U) (hcomm : l * μ = μ * l) (hμ : μ = Gg * β * Gg⁻¹)
    (hα : α = U * μ * U⁻¹) (hR : R = α * β⁻¹ * α⁻¹ * β) (hh : h = R * β⁻¹ * α)
    (hz : U⁻¹ * R * U = z₀) (hGU : Gg * U = Λ) (hM : Gg * R⁻¹ * M * R * Gg⁻¹ = Λ⁻¹) :
    z₀ = compMer μ (Λ⁻¹ * μ * Λ) ∧
      l = μ ^ 2 * Λ * μ⁻¹ * Λ⁻¹ * μ * (Λ⁻¹ * μ * Λ)⁻¹ * μ⁻¹ := by
  have hβ : β = Gg⁻¹ * μ * Gg := by rw [hμ]; group
  have hGg : Gg = Λ * U⁻¹ := by rw [← hGU]; group
  have hM' : M = R * Gg⁻¹ * Λ⁻¹ * Gg * R⁻¹ := by
    calc M = R * Gg⁻¹ * (Gg * R⁻¹ * M * R * Gg⁻¹) * Gg * R⁻¹ := by group
      _ = _ := by rw [hM]
  have hc : Commute l μ := hcomm
  clear hμ hM hcomm
  subst hz hh hM' hR hα hβ hGg
  refine ⟨by rw [compMer]; group, ?_⟩
  have hE : l = Λ * μ⁻¹ * Λ⁻¹ * μ * Λ⁻¹ * μ⁻¹ * Λ * μ := by rw [hl]; group
  calc l = μ ^ 2 * l * (μ ^ 2)⁻¹ := by rw [← (hc.pow_right 2).eq]; group
    _ = μ ^ 2 * (Λ * μ⁻¹ * Λ⁻¹ * μ * Λ⁻¹ * μ⁻¹ * Λ * μ) * (μ ^ 2)⁻¹ := by rw [← hE]
    _ = _ := by group

/-- T-CLASS (knot): the group of `Wh⁻₀(T(r, s))` carries the Whitehead satellite structure over
`T(r, s)` with its own meridian and preferred longitude. -/
theorem isWhSatellite_pairWhiteheadKnot {r s : ℕ} (h : IsTorusPair r s) :
    IsWhSatellite (torusPairKnot r s h) (pairWhiteheadKnot r s h) := by
  have hgap : PairGapRels r s (pairKLoop h) := pairGapRels_of_hom h (MonoidHom.id _)
  have hfix := pairCompTuple_fixed h (pairKLoop h) hgap
  let φ : KnotGroup (torusPairKnot r s h) →* KnotGroup (pairWhiteheadKnot r s h) :=
    PresentedGroup.toGroup (f := pairCompTuple r s (pairKLoop h))
      (lift_artinRels_of_fixed_peri (torusPairKnot r s h) _ hfix)
  have hφ : ∀ k, φ (PresentedGroup.of k) = pairCompTuple r s (pairKLoop h) k := fun k ↦
    PresentedGroup.toGroup.of _
  have hmer : φ (meridian (torusPairKnot r s h)) = pairCompFun r s (pairKLoop h) 0 := hφ _
  have hlon : φ (longitude (torusPairKnot r s h)) = pairCompLong r s (pairKLoop h) := by
    rw [longitude_torusPairKnot, map_mul, map_zpow, map_pow, hmer, pairCompLong, torusFullProd,
      map_list_prod]
    have hl : ∀ l : List (Fin r), List.map φ (List.map (fun j : Fin r ↦
        (PresentedGroup.of (rels := artinRels (torusPairKnot r s h)) j)) l) =
        l.map (pairCompTuple r s (pairKLoop h)) := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => exact congrArg₂ List.cons (hφ a) ih
    exact congrArg (fun x ↦ x.prod ^ s * pairCompFun r s (pairKLoop h) 0 ^ (-((r * s : ℕ) : ℤ)))
      (hl (List.finRange r))
  obtain ⟨Gg, M, U, hl, hμ, hα, hz, hGU, hM⟩ := pairOrbit_split h
  obtain ⟨hH1, hH2⟩ := pairHopf_loops h (pairKGen h)
  have hC : pairKLoop h (pairIdxC r s) * pairKLoop h (pairIdxR r s 0) = 1 := by
    have h0 := hgap.stairLow 0 (Nat.zero_le _)
    simpa [descProd] using h0
  have hR := pairWh_clasp _ _ _ _ _ _ hC hgap.top hH1 hH2
  have hcomm := (map_longitude_eq_orbitLoop (pairWhiteheadKnot r s h) (pairBlocks r s) rfl
    (pairBlocks_valid h) (MonoidHom.id _))
  simp only [MonoidHom.id_apply] at hcomm
  have hlm : longitude (pairWhiteheadKnot r s h) * meridian (pairWhiteheadKnot r s h) =
      meridian (pairWhiteheadKnot r s h) * longitude (pairWhiteheadKnot r s h) := by
    rw [hcomm.1]; exact hcomm.2
  obtain ⟨h1, h2⟩ := pairWh_algebra _ _ _ _ _ _ _ _ _ _ _ hl hlm hμ hα hR hH1 hz hGU hM
  refine ⟨φ, (pairCompLong r s (pairKLoop h))⁻¹ * meridian _ * pairCompLong r s (pairKLoop h),
    ?_, ?_, ?_⟩
  · rw [hmer, h1]
  · rw [hlon]
  · rw [hlon, h2]

end AJConjecture
