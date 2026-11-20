import Mathlib
import AJTwist.Classical.TwCPeripheral

/-!
# The pattern relations of a fixed tuple of a twisted double (PpA)

The forward computation of package TwC (`AJTwist.Classical.TwCPeripheral`:
`isTwWhSatellite_twWhiteheadKnot`, `isTwWhSatelliteP_twWhiteheadKnot`) is proved there for the
tuple of generators of the knot group and returns the companion homomorphism existentially. Its
ingredients hold for every tuple fixed by the block list, in every group; here they are
assembled in that generality, with the companion data written out, so that the longitude of a
representation built from a fixed tuple can be computed.

For a tuple `F` fixed by the run of `twBlocks r s ℓ σ` whose orbit loop commutes with its bottom
edge meridian `μ = edgeMer F 0` (automatic for the tuple of a representation:
`map_longitude_eq_orbitLoop`), with `L = twcLoop r s ℓ σ F`, `z₀ = pairCompFun r s L 0` (the
image of the companion meridian) and `t = pairCompLong r s L * z₀ ^ ℓ` (the image of
`λ_C μ_C^ℓ`):

* `ppa_isWhPattern_of_fixed_neg` (`σ = true`): `IsWhPattern μ t z₀ (orbitLoop F)`;
* `ppa_isWhPattern_of_fixed_pos` (`σ = false`): `IsWhPattern μ t⁻¹ z₀ (orbitLoop F)⁻¹`.

Route: the proofs of the two theorems of `TwCPeripheral` from the step "obtain
`twcOrbit_split_neg`" on: `pairGapRels_twcLoop`, `twcOrbit_split_neg` / `_pos`,
`twcHopf_neg` / `_pos`, `PairGapRels.stairLow 0` and `.top`, `twcPattern_neg` / `_pos`; all are
stated for an arbitrary fixed tuple. For `σ = false`, `twcPattern_pos` also needs
`t * z₀ = z₀ * t`: `pairCompTuple_fixed` gives the companion homomorphism `φ` with
`φ μ_C = z₀`, `φ λ_C = pairCompLong r s L` (`longitude_torusPairKnot`), and `λ_C` commutes with
`μ_C` (`commute_meridian_longitude`; this is the private `exists_compHom_twCPeripheral`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The braid relations hold for a tuple fixed by the braid. -/
private theorem lift_artinRels_of_fixed_ppaForward (K : BraidKnot)
    (f : Fin K.strands → G) (hf : (braidRun K.strands K.word f).1 = f) :
    ∀ x ∈ artinRels K, FreeGroup.lift f x = 1 := by
  rintro _ ⟨k, rfl⟩
  rw [map_mul, map_inv, FreeGroup.lift_apply_of, map_mul, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one, lift_artinWord_snd, ← braidRun_fst_apply, hf]

/-- The companion longitude of loops with the gap relations commutes with the companion
meridian: both are images of the peripheral elements of `T(r, s)`. -/
private theorem commute_compFun_compLong_ppaForward {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hgap : PairGapRels r s L) : Commute (pairCompFun r s L 0) (pairCompLong r s L) := by
  have hfix := pairCompTuple_fixed h L hgap
  let φ : KnotGroup (torusPairKnot r s h) →* G :=
    PresentedGroup.toGroup (f := pairCompTuple r s L)
      (lift_artinRels_of_fixed_ppaForward (torusPairKnot r s h) _ hfix)
  have hφ : ∀ k, φ (PresentedGroup.of k) = pairCompTuple r s L k := fun k ↦
    PresentedGroup.toGroup.of _
  have hmer : φ (meridian (torusPairKnot r s h)) = pairCompFun r s L 0 := hφ _
  have hlon : φ (longitude (torusPairKnot r s h)) = pairCompLong r s L := by
    rw [longitude_torusPairKnot, map_mul, map_zpow, map_pow, hmer, pairCompLong, torusFullProd,
      map_list_prod]
    have hl : ∀ l : List (Fin r), List.map φ (List.map (fun j : Fin r ↦
        (PresentedGroup.of (rels := artinRels (torusPairKnot r s h)) j)) l) =
        l.map (pairCompTuple r s L) := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => exact congrArg₂ List.cons (hφ a) ih
    exact congrArg (fun x ↦ x.prod ^ s * pairCompFun r s L 0 ^ (-((r * s : ℕ) : ℤ)))
      (hl (List.finRange r))
  rw [← hmer, ← hlon]
  exact (commute_meridian_longitude (torusPairKnot r s h)).map φ

/-- Negative clasp: a fixed tuple of `twBlocks r s ℓ true` satisfies the pattern relations with
axis meridian the image of `λ_C μ_C^ℓ`. -/
theorem ppa_isWhPattern_of_fixed_neg {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ true) F = F)
    (hcomm : orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ true) F * edgeMer F 0 =
      edgeMer F 0 * orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ true) F) :
    IsWhPattern (edgeMer F 0)
      (pairCompLong r s (twcLoop r s ℓ true F) * pairCompFun r s (twcLoop r s ℓ true F) 0 ^ ℓ)
      (pairCompFun r s (twcLoop r s ℓ true F) 0)
      (orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ true) F) := by
  have hgap := pairGapRels_twcLoop h ℓ true F hF
  obtain ⟨Gg, M, U, hl, hμ, hα, hz, hGU, hM⟩ := twcOrbit_split_neg h ℓ F hF
  obtain ⟨hH1, hH2⟩ := twcHopf_neg h ℓ F hF
  have hC : twcLoop r s ℓ true F (pairIdxC r s) * twcLoop r s ℓ true F (pairIdxR r s 0) = 1 := by
    have h0 := hgap.stairLow 0 (Nat.zero_le _)
    simpa [descProd] using h0
  exact twcPattern_neg _ _ _ _ _ _ _ _ _ _ _ _ _ hl hcomm hμ hα hC hgap.top hH1 hH2 hz hGU hM

/-- Positive clasp: a fixed tuple of `twBlocks r s ℓ false` satisfies the pattern relations for
the inverse axis meridian and the inverse longitude. -/
theorem ppa_isWhPattern_of_fixed_pos {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ false) F = F)
    (hcomm : orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ false) F * edgeMer F 0 =
      edgeMer F 0 * orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ false) F) :
    IsWhPattern (edgeMer F 0)
      (pairCompLong r s (twcLoop r s ℓ false F) *
        pairCompFun r s (twcLoop r s ℓ false F) 0 ^ ℓ)⁻¹
      (pairCompFun r s (twcLoop r s ℓ false F) 0)
      (orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ false) F)⁻¹ := by
  have hgap := pairGapRels_twcLoop h ℓ false F hF
  have hcl := commute_compFun_compLong_ppaForward h _ hgap
  obtain ⟨Gg, M, U, hl, hμ, hα, hz, hGU, hM⟩ := twcOrbit_split_pos h ℓ F hF
  obtain ⟨hH1, hH2⟩ := twcHopf_pos h ℓ F hF
  have hC : twcLoop r s ℓ false F (pairIdxC r s) * twcLoop r s ℓ false F (pairIdxR r s 0) =
      1 := by
    have h0 := hgap.stairLow 0 (Nat.zero_le _)
    simpa [descProd] using h0
  exact twcPattern_pos _ _ _ _ _ _ _ _ _ _ _ _ _ hl hcomm hμ hα hC hgap.top hH1 hH2 hz hGU hM
    ((hcl.symm.mul_left (Commute.zpow_left (Commute.refl _) ℓ)).eq)

end AJConjecture
