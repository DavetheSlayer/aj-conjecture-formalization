import Mathlib
import AJHandoff.TorusKnot.PairKPeriComp
import AJHandoff.TorusKnot.PairKPeriHopf
import AJHandoff.TorusKnot.PairKOrbSegments
import AJHandoff.TorusKnot.PairKOrbComp

/-!
# The orbit loop of `pairBlocks r s`

The orbit of the strand `0` under `stPerm (pairBlocks r s)` passes through the top annulus
strand `T = 2c - 1`, later through the strand `pairOrbH1 = 2c - s - 1` whose loop is the first
Hopf loop `H₁`, and then through the Hopf strand `2c`. The strand `T` collects `H₂ = H₁⁻¹` first,
and no other strand collects a Hopf loop. Cutting the orbit loop there gives
`λ = G H₁⁻¹ M H₁ U`, where `G` is the product of the strand loops from `0` up to `T`, `M` the
companion part between the two Hopf loops and `U` the product from `2c` back to `0`; the edge
relations along the orbit give `μ = G e_T G⁻¹` and `e_(2c) = U μ U⁻¹`. In terms of the companion
tuple `z` (`AJHandoff.TorusKnot.PairKPeriComp`) and `Λ = pairCompLong`:
`U⁻¹ R_0 U = z_0`, `G U = Λ` and `G R_0⁻¹ M R_0 G⁻¹ = Λ⁻¹`.

Route (without enumerating the orbit, which visits the conveyor strands in a `T(r, s)`-type order
depending on `s mod r`): the orbit enters the top block `[c - s + 1, T]` once, at `T`, and leaves
it once, from `pairOrbH1` to `2c` (`pairOrb_top_iff`, `pairOrb_idx_order`); every strand loop off
`T` and `pairOrbH1` is a pure step `K ^ w y_ℓ ^ n` in the frame of `R_0 = y_0`
(`AJHandoff.TorusKnot.PairKOrbStrand`), and pure steps multiply, so each piece of the orbit is
computed by summing the exponents over its block of positions
(`AJHandoff.TorusKnot.PairKOrbSegments`). The companion tuple is expressed in the rounds by
`pairOrb_compFun_zero`, `pairOrb_compLong`.

All six identities were checked numerically (random `SU(3)` representations of the window) for
`(r, s) ∈ {(2,5), (3,4), (3,5), (3,7), (3,8), (4,5), (4,7), (5,7), (4,9), (5,8), (3,11), (6,7)}`,
and every intermediate identity of the route exactly in the torus knot group
(`AJHandoff.TorusKnot.PairKOrbDefs`).
-/

namespace AJConjecture

section Alg
variable {G : Type*} [Group G]

/-- Conjugation by `y` undone. -/
private theorem orb_unconj (y x z : G) (hx : y * x * y⁻¹ = z) : x = y⁻¹ * z * y := by
  rw [← hx]; group

/-- The companion meridian from the bottom piece `U`. -/
private theorem orb_alg_U (y0 y1 K U : G) (W N : ℤ) (hU : y0 * U * y0⁻¹ = K ^ W * y1 ^ N)
    (hy : y0 = K ^ W * y1 * K ^ (-W)) : U⁻¹ * y0 * U = y0⁻¹ * y1 * y0 := by
  have hU' := orb_unconj y0 U _ hU
  have hk : K ^ (-W) * y0 * K ^ W = y1 := by rw [hy]; group
  calc U⁻¹ * y0 * U = y0⁻¹ * y1 ^ (-N) * (K ^ (-W) * y0 * K ^ W) * y1 ^ N * y0 := by
        rw [hU']; group
    _ = y0⁻¹ * y1 * y0 := by rw [hk]; group

/-- Conjugating by an element that commutes. -/
private theorem orb_conj_comm (y X : G) (h : Commute X y) : y⁻¹ * X * y = X := by
  rw [mul_assoc, h.eq, inv_mul_cancel_left]

/-- The final group theory of the orbit split. -/
private theorem orb_alg_M (y K Gg U M Lam : G) (b : ℤ) (hKy : Commute K y)
    (hUG : y * (U * Gg) * y⁻¹ = K * y ^ (-b)) (hM : y * M * y⁻¹ = K⁻¹ * y ^ b)
    (hLam : Gg * U = Lam) : Gg * y⁻¹ * M * y * Gg⁻¹ = Lam⁻¹ := by
  have hM' : M = K⁻¹ * y ^ b := by
    rw [orb_unconj y M _ hM]
    exact orb_conj_comm y _ (hKy.inv_left.mul_left (Commute.zpow_self y b))
  have hUG' : U * Gg = K * y ^ (-b) := by
    rw [orb_unconj y _ _ hUG]
    exact orb_conj_comm y _ (hKy.mul_left (Commute.zpow_self y (-b)))
  have h1 : y⁻¹ * M * y = (U * Gg)⁻¹ := by
    rw [orb_conj_comm y M (by rw [hM']; exact hKy.inv_left.mul_left (Commute.zpow_self y b)),
      hM', hUG', mul_inv_rev, zpow_neg, inv_inv]
    exact ((hKy.zpow_right b).inv_left).eq
  calc Gg * y⁻¹ * M * y * Gg⁻¹ = Gg * (y⁻¹ * M * y) * Gg⁻¹ := by group
    _ = (Gg * U)⁻¹ := by rw [h1]; group
    _ = Lam⁻¹ := by rw [hLam]

end Alg

/-- `pairOrbit_split` for the generators `pairOrbGen h`. -/
theorem pairOrbit_split_gen {r s : ℕ} (h : IsTorusPair r s) :
    ∃ Gg M U : KnotGroup (pairWhiteheadKnot r s h),
      longitude (pairWhiteheadKnot r s h) =
          Gg * (loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairIdxH1 r s))⁻¹ * M *
            loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairIdxH1 r s) * U ∧
        meridian (pairWhiteheadKnot r s h) = Gg * edgeMer (pairOrbGen h) (pairTop r s) * Gg⁻¹ ∧
        edgeMer (pairOrbGen h) (pairTop r s + 1) = U * meridian (pairWhiteheadKnot r s h) * U⁻¹ ∧
        U⁻¹ * loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairIdxR r s 0) * U =
          pairCompFun r s (loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h)) 0 ∧
        Gg * U = pairCompLong r s (loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h)) ∧
        Gg * (loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairIdxR r s 0))⁻¹ * M *
            loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairIdxR r s 0) * Gg⁻¹ =
          (pairCompLong r s (loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h)))⁻¹ := by
  have hL : PairGapRels r s (loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h)) :=
    pairGapRels_of_hom h (MonoidHom.id _)
  obtain ⟨hiT0, hiTH, hiH, h2c⟩ := pairOrb_idx_order h
  obtain ⟨hTop, hH1top, -, -, hH1T, h2cm⟩ := pairOrbTop_basic h
  have hTm : pairTop r s < pairStrands r s := by simp only [pairTop, pairStrands]; omega
  have hH1m : pairOrbH1 r s < pairStrands r s := by
    simp only [pairOrbH1, pairStrands]; omega
  have hT := (pairOrbIdx_spec h hTm).2
  have hH := (pairOrbIdx_spec h hH1m).2
  have hy0 : pairOrbY r s (loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h)) 0 =
      loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairIdxR r s 0) := by
    have := pairOrbY_natCast (r := r) (s := s)
      (loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h)) (i := 0) (by have := h.2.1; omega)
    rwa [Nat.cast_zero] at this
  -- the strand loop of `pairOrbH1` is `H₁`
  have hSH : stLoop (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairOrbH1 r s) =
      loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairIdxH1 r s) := by
    rw [stLoop_pairBlocks_core h _ hH1m, pairOrbCore]
    obtain ⟨hr, hrs, hcs, hE⟩ := pairOrb_arith h
    have : ¬ (pairOrbH1 r s + 2 ≤ r ∨ pairOrbH1 r s = 2 * pairC r s) := by
      simp only [pairOrbH1, PairOrbTop, pairTop] at hH1top ⊢; omega
    have e1 : ¬ pairOrbH1 r s + s ≤ pairC r s := by simp only [pairOrbH1]; omega
    have e2 : ¬ pairOrbH1 r s + s + r ≤ 2 * pairC r s := by simp only [pairOrbH1]; omega
    have e3 : ¬ pairOrbH1 r s + s + 2 ≤ 2 * pairC r s := by simp only [pairOrbH1]; omega
    have e4 : pairOrbH1 r s + s + 1 = 2 * pairC r s := by simp only [pairOrbH1]; omega
    simp only [hH1T, this, e1, e2, e3, e4, ite_false, ite_true, one_mul]
  have htop := eq_inv_of_mul_eq_one_left hL.top
  -- the longitude
  have hlon := map_longitude_eq_orbitLoop (pairWhiteheadKnot r s h) (pairBlocks r s) rfl
    (pairBlocks_valid h) (MonoidHom.id _)
  simp only [MonoidHom.id_apply] at hlon
  have hlonSeg : longitude (pairWhiteheadKnot r s h) =
      pairOrbSeg r s (pairOrbGen h) 0 (pairStrands r s) := by
    rw [hlon.1, ← orbitLoop_eq_pairOrbSeg]; rfl
  have hsplit : longitude (pairWhiteheadKnot r s h) =
      pairOrbSeg r s (pairOrbGen h) 0 (pairOrbIdx r s (pairTop r s)) *
        pairOrbSeg r s (pairOrbGen h) (pairOrbIdx r s (pairTop r s))
          (pairOrbIdx r s (pairOrbH1 r s)) *
        loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairIdxH1 r s) *
        pairOrbSeg r s (pairOrbGen h) (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s) := by
    rw [hlonSeg, pairOrbSeg_split r s _ (b := pairOrbIdx r s (pairTop r s)) (Nat.zero_le _)
        (by omega),
      pairOrbSeg_split r s _ (b := pairOrbIdx r s (pairOrbH1 r s)) (le_of_lt hiTH) (by omega),
      pairOrbSeg_split r s _ (b := pairOrbIdx r s (pairOrbH1 r s) + 1) (Nat.le_succ _)
        (by omega), pairOrbSeg_one, hH, hSH]
    group
  have h5 : pairOrbSeg r s (pairOrbGen h) 0 (pairOrbIdx r s (pairTop r s)) *
      pairOrbSeg r s (pairOrbGen h) (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s) =
      pairCompLong r s (loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h)) := by
    rw [orb_unconj _ _ _ (pairOrb_seg_GU h _ hL), pairOrb_compLong h hL]
    simp only [mul_assoc]
  refine ⟨pairOrbSeg r s (pairOrbGen h) 0 (pairOrbIdx r s (pairTop r s)),
    (loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h) (pairIdxH2 r s))⁻¹ *
      pairOrbSeg r s (pairOrbGen h) (pairOrbIdx r s (pairTop r s)) (pairOrbIdx r s (pairOrbH1 r s)),
    pairOrbSeg r s (pairOrbGen h) (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsplit, htop]
    group
  · have he := pairOrb_edgeMer_seg h (k := pairOrbIdx r s (pairTop r s)) (by omega)
    rw [hT] at he
    rw [he]
    group
  · have he := pairOrb_edgeMer_seg h (k := pairOrbIdx r s (pairOrbH1 r s) + 1) (by omega)
    rw [h2c] at he
    have hc : longitude (pairWhiteheadKnot r s h) * meridian (pairWhiteheadKnot r s h) =
        meridian (pairWhiteheadKnot r s h) * longitude (pairWhiteheadKnot r s h) := by
      rw [hlon.1]; exact hlon.2
    rw [hlonSeg, pairOrbSeg_split r s _ (b := pairOrbIdx r s (pairOrbH1 r s) + 1)
      (Nat.zero_le _) (by omega)] at hc
    have hT1 : pairTop r s + 1 = 2 * pairC r s := by
      simp only [PairOrbTop, pairTop] at hTop ⊢; omega
    rw [hT1, he]
    generalize pairOrbSeg r s (pairOrbGen h) 0 (pairOrbIdx r s (pairOrbH1 r s) + 1) = A at hc ⊢
    generalize pairOrbSeg r s (pairOrbGen h) (pairOrbIdx r s (pairOrbH1 r s) + 1)
      (pairStrands r s) = B at hc ⊢
    generalize meridian (pairWhiteheadKnot r s h) = μ at hc ⊢
    calc A⁻¹ * μ * A = A⁻¹ * (μ * (A * B)) * B⁻¹ := by group
      _ = A⁻¹ * (A * B * μ) * B⁻¹ := by rw [hc]
      _ = B * μ * B⁻¹ := by group
  · obtain ⟨W, N, hU, hy⟩ := pairOrb_seg_U h _ hL
    rw [pairOrb_compFun_zero h hL, ← hy0]
    exact orb_alg_U _ _ _ _ W N hU hy
  · exact h5
  · have hKy : Commute (pairOrbK r s (loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h)) ^
        (s : ℤ)) (pairOrbY r s (loopAt (pairStrands r s) (pairBlocks r s) (pairOrbGen h)) 0) := by
      have hk := pairOrbK_zpow_conj h hL 0 (s : ℤ)
      rw [zero_add, mul_comm (r : ℤ), ← zero_add ((s : ℤ) * r), pairOrbY_add_mul_period] at hk
      exact (mul_inv_eq_iff_eq_mul.1 (by rw [← zpow_neg]; exact hk))
    rw [← hy0]
    refine orb_alg_M _ _ _ _ _ _ ((r * s : ℕ) : ℤ) hKy (pairOrb_seg_UG h _ hL) ?_ h5
    rw [← zpow_neg]
    exact pairOrb_seg_M h _ hL

/-- The generators of the knot group of `pairWhiteheadKnot r s h`. -/
abbrev pairKGen {r s : ℕ} (h : IsTorusPair r s) :
    Fin (pairStrands r s) → KnotGroup (pairWhiteheadKnot r s h) :=
  fun t ↦ PresentedGroup.of t

/-- The block loops of `pairBlocks r s` on the generators of the knot group. -/
abbrev pairKLoop {r s : ℕ} (h : IsTorusPair r s) : ℕ → KnotGroup (pairWhiteheadKnot r s h) :=
  loopAt (pairStrands r s) (pairBlocks r s) (pairKGen h)

/-- The orbit loop of the strand `0` of `pairBlocks r s`, cut at the two Hopf loops, and the
three identities tying its pieces to the companion tuple. -/
theorem pairOrbit_split {r s : ℕ} (h : IsTorusPair r s) :
    ∃ Gg M U : KnotGroup (pairWhiteheadKnot r s h),
      longitude (pairWhiteheadKnot r s h) =
          Gg * (pairKLoop h (pairIdxH1 r s))⁻¹ * M * pairKLoop h (pairIdxH1 r s) * U ∧
        meridian (pairWhiteheadKnot r s h) = Gg * edgeMer (pairKGen h) (pairTop r s) * Gg⁻¹ ∧
        edgeMer (pairKGen h) (pairTop r s + 1) = U * meridian (pairWhiteheadKnot r s h) * U⁻¹ ∧
        U⁻¹ * pairKLoop h (pairIdxR r s 0) * U = pairCompFun r s (pairKLoop h) 0 ∧
        Gg * U = pairCompLong r s (pairKLoop h) ∧
        Gg * (pairKLoop h (pairIdxR r s 0))⁻¹ * M * pairKLoop h (pairIdxR r s 0) * Gg⁻¹ =
          (pairCompLong r s (pairKLoop h))⁻¹ :=
  pairOrbit_split_gen h

end AJConjecture
