import Mathlib
import AJFamily.Classical.SatelliteData
import AJPaper.Filling.PpAGlue
import AJPaper.Filling.PpAPattern
import AJPaper.Filling.PpATwistForward

/-!
# The representations of the twist knot groups at the points of `𝒫_(-ℓ) = 0` (PpA, claim 1)

Source: arXiv:2611.24826v1, Section 7.6 (`classical.tex`): "Set `Y = W^k` and `X = Q₀⁻¹`. …
The pattern relator … holds because `Y = W^k`. The filling relation holds by construction.
Evaluating the outer word now gives the same `L`."

* `ppa_exists_twistFixedTuple`: for `a`, `c` in a group with `c = compMer a (c^(-ℓ) a c^ℓ)` there
  is a tuple fixed by the run of `ppaTwistBlocks ℓ` with bottom edge meridian `a` and chain
  loop `c⁻¹`.
* `ppa_exists_rep_twistKnot`: the corresponding homomorphism from the knot group of
  `ppaTwistKnot ℓ`, with meridian `a` and longitude `a² t a⁻¹ t⁻¹ a (t⁻¹ a t)⁻¹ a⁻¹`, `t = c^ℓ`.
* `ppa_mem_eigenvalueSet_twistKnot`: every zero `(M, L)` of `𝒫_(-ℓ)` with `M ≠ 0`, `M⁴ ≠ 1`,
  `M² + L ≠ 0` is a point of the eigenvalue set of `ppaTwistKnot ℓ`.

Route for the tuple: `ppa_exists_fixedTuple_of_edges` with `M = 3`, `j₀ = 1`,
`tail = ppaTwistTail`, the loops `Lb = (c⁻¹, H, c, H⁻¹)` of the untwisted list
`[σ_0, σ_1⁻¹, σ_0⁻¹, σ_1⁻¹]`, and the edge meridians
`e_0 = a`, `e_1 = c^(ℓ-1) a c^(-ℓ)` (`ppaChainTop ℓ a c⁻¹`), `H = c⁻¹ a e_1⁻¹`,
`e_2 = H e_1 = c⁻¹ a`, and `ppaChainEdge 3 ℓ a c⁻¹` on the new levels.
The gap products of the untwisted list are `c c⁻¹` at the level `1` and `H⁻¹ H` at the level
`2`. The three equations of the tail (`loopPr_neg_edge`): `σ_0⁻¹` (loop `c`) holds by the
definition of `H`, the second `σ_1⁻¹` (loop `H⁻¹`) by the definition of `e_2`, and the first
`σ_1⁻¹` (loop `H`) is `H e_1 = e_1 c H`, i.e. `c = a e_1 a⁻¹ e_1⁻¹`; with `u = c^ℓ` this reads
`c = u (a u⁻¹ a⁻¹ u a⁻¹ u⁻¹ a u) u⁻¹`, which is `hmer` conjugated by `u` (`u` commutes with
`c`).
Route for the representation: as `ppa_exists_rep_twWhiteheadKnot_neg`
(`AJPaper.Filling.PpARealize`): `PresentedGroup.toGroup`, `map_longitude_eq_orbitLoop`,
`ppa_twistPattern_of_fixed` with chain loop `c⁻¹`. The points: `ppa_exists_pattern_point (-ℓ)`
as in `ppa_mem_eigenvalueSet_neg` (for `ℓ = 0`, `𝒫_0 = 1` has no zero).

Checked numerically (`SCR/A/py/twistrep.py`, 100 digits, `|ℓ| ≤ 3`: the tuple is fixed, the
library's longitude is the word and its eigenvalue is a root of `𝒫_(-ℓ)(M, ·)`), and on the
Lean objects in dihedral groups (`SCR/A/lean/TestTwistTuple.lean`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The braid relations hold for a tuple fixed by the braid. -/
private theorem lift_artinRels_of_fixed_ppaTwistTuple (K : BraidKnot)
    (f : Fin K.strands → G) (hf : (braidRun K.strands K.word f).1 = f) :
    ∀ x ∈ artinRels K, FreeGroup.lift f x = 1 := by
  rintro _ ⟨k, rfl⟩
  rw [map_mul, map_inv, FreeGroup.lift_apply_of, map_mul, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one, lift_artinWord_snd, ← braidRun_fst_apply, hf]

/-- The descending products of at most three edge meridians. -/
private theorem descProd_small_ppaTwistTuple (e : ℕ → G) :
    descProd e 0 0 = 1 ∧ descProd e 0 1 = e 0 ∧ descProd e 0 2 = e 1 * e 0 ∧
      descProd e 0 3 = e 2 * e 1 * e 0 := by
  simp [descProd, List.range_succ, mul_assoc]

/-- The clasp relation in terms of the edge meridian of the level `1`. -/
private theorem clasp_edge_ppaTwistTuple (ℓ : ℤ) (a c : G)
    (hmer : c = compMer a ((c ^ ℓ)⁻¹ * a * c ^ ℓ)) :
    c = a * ppaChainTop ℓ a c⁻¹ * a⁻¹ * (ppaChainTop ℓ a c⁻¹)⁻¹ := by
  calc c = a * c⁻¹ * (c ^ ℓ * c * (c ^ ℓ)⁻¹) * a⁻¹ * c := by group
    _ = a * c⁻¹ * (c ^ ℓ * compMer a ((c ^ ℓ)⁻¹ * a * c ^ ℓ) * (c ^ ℓ)⁻¹) * a⁻¹ * c := by
        rw [← hmer]
    _ = _ := by rw [compMer, ppaChainTop]; group

/-- The fixed tuple of the block list of the twist knot `Z_ℓ` with meridian `a` and axis
longitude `c`. -/
theorem ppa_exists_twistFixedTuple (ℓ : ℤ) (a c : G)
    (hmer : c = compMer a ((c ^ ℓ)⁻¹ * a * c ^ ℓ)) :
    ∃ F : Fin (3 + twExtra ℓ) → G,
      runTop (3 + twExtra ℓ) (ppaTwistBlocks ℓ) F = F ∧ edgeMer F 0 = a ∧
        twcChainLoop 3 1 ℓ F = c⁻¹ := by
  have hc := clasp_edge_ppaTwistTuple ℓ a c hmer
  have hkey : c⁻¹ * a * (ppaChainTop ℓ a c⁻¹)⁻¹ = c⁻¹ * (ppaChainTop ℓ a c⁻¹)⁻¹ * c⁻¹ * a := by
    calc c⁻¹ * a * (ppaChainTop ℓ a c⁻¹)⁻¹
        = c⁻¹ * (ppaChainTop ℓ a c⁻¹)⁻¹ *
          (a * ppaChainTop ℓ a c⁻¹ * a⁻¹ * (ppaChainTop ℓ a c⁻¹)⁻¹)⁻¹ * a := by group
      _ = _ := by rw [← hc]
  obtain ⟨Lb, hL0, hL1, hL2, hL3⟩ : ∃ Lb : ℕ → G, Lb 0 = c⁻¹ ∧
      Lb 1 = c⁻¹ * a * (ppaChainTop ℓ a c⁻¹)⁻¹ ∧ Lb 2 = c ∧
      Lb 3 = (c⁻¹ * a * (ppaChainTop ℓ a c⁻¹)⁻¹)⁻¹ :=
    ⟨fun q ↦ if q = 0 then c⁻¹ else if q = 1 then c⁻¹ * a * (ppaChainTop ℓ a c⁻¹)⁻¹
      else if q = 2 then c else (c⁻¹ * a * (ppaChainTop ℓ a c⁻¹)⁻¹)⁻¹, rfl, rfl, rfl, rfl⟩
  obtain ⟨e, he0, he1, he2, he⟩ : ∃ e : ℕ → G, e 0 = a ∧ e 1 = ppaChainTop ℓ a c⁻¹ ∧
      e 2 = c⁻¹ * a ∧ ∀ n, 3 ≤ n → e n = ppaChainEdge 3 ℓ a c⁻¹ n :=
    ⟨fun n ↦ if n = 0 then a else if n = 1 then ppaChainTop ℓ a c⁻¹
      else if n = 2 then c⁻¹ * a else ppaChainEdge 3 ℓ a c⁻¹ n, rfl, rfl, rfl,
      fun n hn ↦ by
        dsimp only
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]⟩
  obtain ⟨hD0, hD1, hD2, hD3⟩ := descProd_small_ppaTwistTuple e
  have hv : ∀ b ∈ ppaTwistTail, b.Valid 3 := by
    intro b hb
    simp only [ppaTwistTail, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp only [SBlock.Valid] <;> omega
  have hgap : ∀ n, gapPrefix (SBlock.band 0 1 :: ppaTwistTail) Lb n = 1 := by
    intro n
    simp only [ppaTwistTail, gapPrefix, SBlock.lo, SBlock.hi, hL0, hL1, hL2, hL3]
    obtain rfl | rfl | hn : n = 1 ∨ n = 2 ∨ (n ≠ 1 ∧ n ≠ 2) := by omega
    · simp
    · simp only [Nat.reduceAdd, le_refl, and_self, ↓reduceIte, one_mul, zero_add,
        Nat.one_le_ofNat, Nat.not_ofNat_le_one, and_false, mul_one, inv_mul_cancel]
    · simp (disch := omega) only [ite_eq_right, mul_one]
  obtain ⟨F, hF, hF0, hFc, -⟩ := ppa_exists_fixedTuple_of_edges (M := 3) (j₀ := 1)
    (by norm_num) (by norm_num) ℓ ppaTwistTail hv Lb hgap a e he0 (by rw [he1, hL0])
    (fun n hn ↦ by rw [he n hn, hL0]) (fun q hq ↦ by
      have hq3 : q < 3 := hq
      interval_cases q
      · simp (decide := true) only [ppaTwistTail, List.getD_cons_zero, List.take_succ_cons,
          List.take_zero, loopPr, gapPrefix, hD1, hD2, hD3, he0, he1, he2, hL0, hL1, ↓reduceIte,
          one_mul]
        refine hkey.trans ?_
        group
      · simp (decide := true) only [ppaTwistTail, List.getD_cons_zero, List.getD_cons_succ,
          List.take_succ_cons, List.take_zero, loopPr, gapPrefix, hD0, hD1, hD2, he0, he1, hL0,
          hL1, hL2, ↓reduceIte, one_mul]
        group
      · simp (decide := true) only [ppaTwistTail, List.getD_cons_zero, List.getD_cons_succ,
          List.take_succ_cons, List.take_zero, loopPr, gapPrefix, hD1, hD2, hD3, he0, he1, he2,
          hL0, hL1, hL2, hL3, ↓reduceIte, one_mul]
        group)
  exact ⟨F, hF, hF0, hFc.trans hL0⟩

/-- The representation of the knot group of the twist knot `Z_ℓ` with meridian `a` and axis
longitude `c`. -/
theorem ppa_exists_rep_twistKnot (ℓ : ℤ) (a c : G)
    (hmer : c = compMer a ((c ^ ℓ)⁻¹ * a * c ^ ℓ)) :
    ∃ ρ : KnotGroup (ppaTwistKnot ℓ) →* G, ρ (meridian (ppaTwistKnot ℓ)) = a ∧
      ρ (longitude (ppaTwistKnot ℓ)) =
        a ^ 2 * c ^ ℓ * a⁻¹ * (c ^ ℓ)⁻¹ * a * ((c ^ ℓ)⁻¹ * a * c ^ ℓ)⁻¹ * a⁻¹ := by
  obtain ⟨F, hF, hF0, hFc⟩ := ppa_exists_twistFixedTuple ℓ a c hmer
  let ρ : KnotGroup (ppaTwistKnot ℓ) →* G :=
    PresentedGroup.toGroup (f := F) (lift_artinRels_of_fixed_ppaTwistTuple (ppaTwistKnot ℓ) F hF)
  have hρ : ∀ t, ρ (PresentedGroup.of t) = F t := fun t ↦ PresentedGroup.toGroup.of _
  have hgen : (fun t : Fin (ppaTwistKnot ℓ).strands ↦ ρ (PresentedGroup.of t)) = F := funext hρ
  have hm : ρ (meridian (ppaTwistKnot ℓ)) = edgeMer F 0 :=
    (hρ _).trans (edgeMer_zero F (ppaTwistKnot ℓ).strands_pos).symm
  obtain ⟨hl, hc⟩ := map_longitude_eq_orbitLoop (ppaTwistKnot ℓ) (ppaTwistBlocks ℓ) rfl
    (ppaTwistBlocks_valid ℓ) ρ
  rw [hgen] at hl hc
  rw [hm] at hc
  have hp := (ppa_twistPattern_of_fixed ℓ F hF hc).2
  rw [hFc, inv_inv, hF0] at hp
  exact ⟨ρ, hm.trans hF0, hl.trans hp⟩

/-- Generic zeros of `𝒫_(-ℓ)` are eigenvalue points of the twist knot `Z_ℓ`. -/
theorem ppa_mem_eigenvalueSet_twistKnot (ℓ : ℤ) {M L : ℂ} (hM : M ≠ 0) (hM4 : M ^ 4 ≠ 1)
    (hQ : M ^ 2 + L ≠ 0) (hP : evalPoint (mapC (twP (-ℓ))) (M, L) = 0) :
    (M, L) ∈ eigenvalueSet (ppaTwistKnot ℓ) := by
  have hℓ : -ℓ ≠ 0 := fun h0 ↦ by
    rw [h0] at hP
    simp [twP_zero, evalPoint, mapC] at hP
  obtain ⟨a, a₁, h1, h2, h3, h4, h5⟩ := ppa_exists_pattern_point (-ℓ) hℓ hM hM4 hQ hP
  rw [zpow_neg, inv_inv] at h4 h5
  have ha₁ : a₁ = (compMer a a₁ ^ ℓ)⁻¹ * a * compMer a a₁ ^ ℓ := by
    rw [zpow_neg] at h3
    rw [← h3]
    group
  obtain ⟨ρ, hm, hl⟩ := ppa_exists_rep_twistKnot ℓ a (compMer a a₁) (congrArg (compMer a) ha₁)
  have hl' : ρ (longitude (ppaTwistKnot ℓ)) =
      a ^ 2 * compMer a a₁ ^ ℓ * a⁻¹ * (compMer a a₁ ^ ℓ)⁻¹ * a * a₁⁻¹ * a⁻¹ := by
    rw [hl, ← ha₁]
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · rw [hm]
    exact h1
  · rw [hl']
    exact h4
  · rw [hm]
    exact h2
  · rw [hl']
    exact h5

end AJConjecture
