import Mathlib
import AJHandoff.TorusKnot.PairKPeriGeneric
import AJTwist.Knot.TwKKnot
import AJTwist.Classical.TwCOrbitSplit
import AJTwist.Classical.TwCHopf
import AJTwist.Classical.TwCPatternAlg

/-!
# The twisted satellite structure of the knots `twWhiteheadKnot r s h ℓ σ` (Unit C2)

For the closed braids of package TwK (`AJTwist.Knot.TwKKnot`):

* `isTwWhSatellite_twWhiteheadKnot`: the knot group of `twWhiteheadKnot r s h ℓ true` carries the
  structure of the `ℓ`-twisted negative-clasp Whitehead double of `T(r, s)`,
  `IsTwWhSatellite (torusPairKnot r s h) _ ℓ`;
* `isTwWhSatelliteP_twWhiteheadKnot`: the knot group of `twWhiteheadKnot r s h ℓ false` carries
  the structure of the positive-clasp double, `IsTwWhSatelliteP (torusPairKnot r s h) _ ℓ`.

With `ℓ = 0`, `σ = true` this is `isWhSatellite_pairWhiteheadKnot`.

Route (as `isWhSatellite_pairWhiteheadKnot`, `AJHandoff.TorusKnot.PairKPeripheral`). Let `F` be
the tuple of the generators of the knot group, fixed by the run of `twBlocks r s ℓ σ`
(`braidRun_fst_of_hom`), and `L = twcLoop r s ℓ σ F`.
1. `pairGapRels_twcLoop` gives `PairGapRels r s L`, hence the companion homomorphism `φ` from
   `pairCompTuple_fixed` by `PresentedGroup.toGroup`, with `φ μ_C = pairCompFun r s L 0` and
   `φ λ_C = pairCompLong r s L` (`longitude_torusPairKnot`), so
   `φ (λ_C μ_C^ℓ) = pairCompLong r s L * pairCompFun r s L 0 ^ ℓ =: t`; `t` commutes with
   `φ μ_C` because `λ_C` commutes with `μ_C`.
2. `twcOrbit_split_neg` / `twcOrbit_split_pos`, with `map_longitude_eq_orbitLoop` for the block
   list `twBlocks r s ℓ σ` (`twBlocks_valid`): the longitude is the orbit loop and commutes
   with the meridian `F 0 = edgeMer F 0`.
3. `twcHopf_neg` / `twcHopf_pos`, and the gap relations `C R_0 = 1` (`stairLow 0`) and
   `H₂ H₁ = 1` (`top`) of `PairGapRels`.
4. `twcPattern_neg` / `twcPattern_pos`.

Checked numerically on `SU(2)` representations of the knot groups (`SCR/C/py/w2_twk_all.py`):
the two pattern relations for `(2,3)`, `ℓ = -1, 1` (negative clasp), `ℓ = -2, 1` (positive);
`(3,4)`, `ℓ = -1, 2` (negative), `ℓ = -2, 1` (positive), with the library's meridian and
longitude.
-/

namespace AJConjecture

/-- The braid relations hold for a tuple fixed by the braid. -/
private theorem lift_artinRels_of_fixed_twCPeripheral {G : Type*} [Group G] (K : BraidKnot)
    (f : Fin K.strands → G) (hf : (braidRun K.strands K.word f).1 = f) :
    ∀ x ∈ artinRels K, FreeGroup.lift f x = 1 := by
  rintro _ ⟨k, rfl⟩
  rw [map_mul, map_inv, FreeGroup.lift_apply_of, map_mul, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one, lift_artinWord_snd, ← braidRun_fst_apply, hf]

/-- The companion homomorphism of loops with the gap relations: it sends the meridian of
`T(r, s)` to `pairCompFun r s L 0`, the longitude to `pairCompLong r s L`, and the two images
commute. -/
private theorem exists_compHom_twCPeripheral {r s : ℕ} (h : IsTorusPair r s) {G : Type*}
    [Group G] (L : ℕ → G) (hgap : PairGapRels r s L) (ℓ : ℤ) :
    ∃ φ : KnotGroup (torusPairKnot r s h) →* G,
      φ (meridian (torusPairKnot r s h)) = pairCompFun r s L 0 ∧
        φ (longitude (torusPairKnot r s h) * meridian (torusPairKnot r s h) ^ ℓ) =
          pairCompLong r s L * pairCompFun r s L 0 ^ ℓ ∧
        pairCompLong r s L * pairCompFun r s L 0 ^ ℓ * pairCompFun r s L 0 =
          pairCompFun r s L 0 * (pairCompLong r s L * pairCompFun r s L 0 ^ ℓ) := by
  have hfix := pairCompTuple_fixed h L hgap
  let φ : KnotGroup (torusPairKnot r s h) →* G :=
    PresentedGroup.toGroup (f := pairCompTuple r s L)
      (lift_artinRels_of_fixed_twCPeripheral (torusPairKnot r s h) _ hfix)
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
  have hcl : Commute (pairCompFun r s L 0) (pairCompLong r s L) := by
    rw [← hmer, ← hlon]
    exact (commute_meridian_longitude (torusPairKnot r s h)).map φ
  refine ⟨φ, hmer, by rw [map_mul, map_zpow, hlon, hmer], ?_⟩
  exact ((hcl.symm.mul_left (Commute.zpow_left (Commute.refl _) ℓ)).eq)

/-- The generators of the knot group of a twisted double form a tuple fixed by the run of its
block list; the meridian is the edge meridian of level `0`, the longitude the orbit loop, and
they commute. -/
private theorem twcKnot_data_twCPeripheral {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool) :
    ∃ F : Fin (twStrands r s ℓ) → KnotGroup (twWhiteheadKnot r s h ℓ σ),
      runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F ∧
        edgeMer F 0 = meridian (twWhiteheadKnot r s h ℓ σ) ∧
        orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ σ) F =
          longitude (twWhiteheadKnot r s h ℓ σ) ∧
        longitude (twWhiteheadKnot r s h ℓ σ) * meridian (twWhiteheadKnot r s h ℓ σ) =
          meridian (twWhiteheadKnot r s h ℓ σ) * longitude (twWhiteheadKnot r s h ℓ σ) := by
  have hlon := map_longitude_eq_orbitLoop (twWhiteheadKnot r s h ℓ σ) (twBlocks r s ℓ σ) rfl
    (twBlocks_valid h ℓ σ) (MonoidHom.id _)
  simp only [MonoidHom.id_apply] at hlon
  refine ⟨fun t ↦ PresentedGroup.of t, braidRun_fst_of_hom (twWhiteheadKnot r s h ℓ σ)
    (MonoidHom.id _), edgeMer_zero _ (twWhiteheadKnot r s h ℓ σ).strands_pos, hlon.1.symm, ?_⟩
  rw [hlon.1]
  exact hlon.2

/-- Unit C2, negative clasp: `W_(-,ℓ)(T(r, s))` as the closed braid `twWhiteheadKnot r s h ℓ true`
has the structure of the `ℓ`-twisted negative-clasp Whitehead double of `T(r, s)`. -/
theorem isTwWhSatellite_twWhiteheadKnot {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) :
    IsTwWhSatellite (torusPairKnot r s h) (twWhiteheadKnot r s h ℓ true) ℓ := by
  obtain ⟨F, hF, hmer, hlon, hcomm⟩ := twcKnot_data_twCPeripheral h ℓ true
  have hgap := pairGapRels_twcLoop h ℓ true F hF
  obtain ⟨φ, hφm, hφl, -⟩ := exists_compHom_twCPeripheral h _ hgap ℓ
  obtain ⟨Gg, M, U, hl, hμ, hα, hz, hGU, hM⟩ := twcOrbit_split_neg h ℓ F hF
  obtain ⟨hH1, hH2⟩ := twcHopf_neg h ℓ F hF
  have hC : twcLoop r s ℓ true F (pairIdxC r s) * twcLoop r s ℓ true F (pairIdxR r s 0) = 1 := by
    have h0 := hgap.stairLow 0 (Nat.zero_le _)
    simpa [descProd] using h0
  rw [hlon] at hl
  rw [hmer] at hμ hα
  refine ⟨φ, ?_⟩
  rw [hφm, hφl]
  exact twcPattern_neg _ _ _ _ _ _ _ _ _ _ _ _ _ hl hcomm hμ hα hC hgap.top hH1 hH2 hz hGU hM

/-- Unit C2, positive clasp: `W_(+,ℓ)(T(r, s))` as the closed braid
`twWhiteheadKnot r s h ℓ false` has the structure of the `ℓ`-twisted positive-clasp Whitehead
double of `T(r, s)`. -/
theorem isTwWhSatelliteP_twWhiteheadKnot {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) :
    IsTwWhSatelliteP (torusPairKnot r s h) (twWhiteheadKnot r s h ℓ false) ℓ := by
  obtain ⟨F, hF, hmer, hlon, hcomm⟩ := twcKnot_data_twCPeripheral h ℓ false
  have hgap := pairGapRels_twcLoop h ℓ false F hF
  obtain ⟨φ, hφm, hφl, htz⟩ := exists_compHom_twCPeripheral h _ hgap ℓ
  obtain ⟨Gg, M, U, hl, hμ, hα, hz, hGU, hM⟩ := twcOrbit_split_pos h ℓ F hF
  obtain ⟨hH1, hH2⟩ := twcHopf_pos h ℓ F hF
  have hC : twcLoop r s ℓ false F (pairIdxC r s) * twcLoop r s ℓ false F (pairIdxR r s 0) =
      1 := by
    have h0 := hgap.stairLow 0 (Nat.zero_le _)
    simpa [descProd] using h0
  rw [hlon] at hl
  rw [hmer] at hμ hα
  refine ⟨φ, ?_⟩
  rw [hφm, hφl]
  exact twcPattern_pos _ _ _ _ _ _ _ _ _ _ _ _ _ hl hcomm hμ hα hC hgap.top hH1 hH2 hz hGU hM
    htz

end AJConjecture
