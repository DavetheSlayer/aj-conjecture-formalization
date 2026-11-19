import Mathlib
import AJHandoff.TorusKnot.PairKPeripheral

/-!
# Reducing the realization of satellite data to a fixed tuple

`pairRealizes_of_fixedTuple`: to realize a companion representation `ψ` and a meridian image
`a` by a representation of the knot group of `Wh⁻₀(T(r, s))`, it suffices to give a tuple `f`
fixed by the run of `pairBlocks r s` with `f 0 = a` whose companion tuple (computed from its
block loops, `pairCompTuple`) is the tuple of the images under `ψ` of Artin's generators of
`T(r, s)`. The longitude is then computed from the forward satellite structure: the knot group
satisfies `λ = μ² Λ μ⁻¹ Λ⁻¹ μ (Λ⁻¹ μ Λ)⁻¹ μ⁻¹` with `Λ = pairCompLong` of its own block loops
(the proof of `isWhSatellite_pairWhiteheadKnot`), and every construction of the chamber-product
method commutes with group homomorphisms.
-/

namespace AJConjecture

section Natural

variable {G H : Type*} [Group G] [Group H]

/-- The run of a braid word commutes with group homomorphisms. -/
theorem braidRun_fst_map (ρ : G →* H) (m : ℕ) (w : BraidWord) (f : Fin m → G) :
    (braidRun m w fun k ↦ ρ (f k)).1 = fun k ↦ ρ ((braidRun m w f).1 k) := by
  have hl : ∀ x, FreeGroup.lift (fun k ↦ ρ (f k)) x = ρ (FreeGroup.lift f x) := fun x ↦ by
    have : (FreeGroup.lift fun k ↦ ρ (f k)) = ρ.comp (FreeGroup.lift f) := by
      ext a
      simp
    rw [this, MonoidHom.comp_apply]
  funext k
  rw [braidRun_fst_apply, braidRun_fst_apply m w f, ← lift_artinWord_snd, ← lift_artinWord_snd,
    hl, map_mul, map_mul, map_inv]

/-- The tuple above a list of blocks commutes with group homomorphisms. -/
theorem runTop_map (ρ : G →* H) (m : ℕ) (bs : List SBlock) (f : Fin m → G) :
    runTop m bs (fun k ↦ ρ (f k)) = fun k ↦ ρ (runTop m bs f k) :=
  braidRun_fst_map ρ m (blocksWord bs) f

/-- The chamber products commute with group homomorphisms. -/
theorem prePr_map (ρ : G →* H) {m : ℕ} (f : Fin m → G) (n : ℕ) :
    prePr (fun k ↦ ρ (f k)) n = ρ (prePr f n) := by
  rw [prePr, prePr, map_list_prod, List.map_take, List.map_ofFn]
  rfl

/-- The loop of a block commutes with group homomorphisms. -/
theorem sBlock_loop_map_rev (ρ : G →* H) {m : ℕ} (f : Fin m → G) (b : SBlock) :
    b.loop (fun k ↦ ρ (f k)) = ρ (b.loop f) := by
  cases b <;> simp only [SBlock.loop, prePr_map, map_mul, map_inv]

/-- The block loops commute with group homomorphisms. -/
theorem loopAt_map (ρ : G →* H) (m : ℕ) (bs : List SBlock) (f : Fin m → G) (q : ℕ) :
    loopAt m bs (fun k ↦ ρ (f k)) q = ρ (loopAt m bs f q) := by
  rw [loopAt, loopAt, runTop_map, sBlock_loop_map_rev]

/-- Descending products commute with group homomorphisms. -/
theorem descProd_map (ρ : G →* H) (g : ℕ → G) (a n : ℕ) :
    descProd (fun i ↦ ρ (g i)) a n = ρ (descProd g a n) := by
  rw [descProd, descProd, map_list_prod, List.map_map]
  rfl

/-- The companion tuple commutes with group homomorphisms. -/
theorem pairCompFun_map (ρ : G →* H) (r s : ℕ) (L : ℕ → G) (k : ℕ) :
    pairCompFun r s (fun q ↦ ρ (L q)) k = ρ (pairCompFun r s L k) := by
  have hw : ∀ n, pairWin r s (fun q ↦ ρ (L q)) n = ρ (pairWin r s L n) := by
    intro n
    unfold pairWin
    split_ifs <;> simp only [descProd_map, map_mul, map_inv]
  simp only [pairCompFun, hw, map_mul, map_inv, map_list_prod, List.map_map]
  rfl

end Natural

/-- The clasp: the two Hopf loops and the relations `C R = 1`, `H₂ H₁ = 1` give
`R = α β⁻¹ α⁻¹ β`. -/
private theorem revWh_clasp {G : Type*} [Group G] (R C h₁ h₂ α β : G) (hC : C * R = 1)
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

/-- The pure group theory of the assembly (as in `isWhSatellite_pairWhiteheadKnot`). -/
private theorem revWh_algebra {G : Type*} [Group G] (μ α β h R Gg M U Λ l : G)
    (hl : l = Gg * h⁻¹ * M * h * U) (hcomm : l * μ = μ * l) (hμ : μ = Gg * β * Gg⁻¹)
    (hα : α = U * μ * U⁻¹) (hR : R = α * β⁻¹ * α⁻¹ * β) (hh : h = R * β⁻¹ * α)
    (hGU : Gg * U = Λ) (hM : Gg * R⁻¹ * M * R * Gg⁻¹ = Λ⁻¹) :
    l = μ ^ 2 * Λ * μ⁻¹ * Λ⁻¹ * μ * (Λ⁻¹ * μ * Λ)⁻¹ * μ⁻¹ := by
  have hβ : β = Gg⁻¹ * μ * Gg := by rw [hμ]; group
  have hGg : Gg = Λ * U⁻¹ := by rw [← hGU]; group
  have hM' : M = R * Gg⁻¹ * Λ⁻¹ * Gg * R⁻¹ := by
    calc M = R * Gg⁻¹ * (Gg * R⁻¹ * M * R * Gg⁻¹) * Gg * R⁻¹ := by group
      _ = _ := by rw [hM]
  have hc : Commute l μ := hcomm
  clear hμ hM hcomm
  subst hh hM' hR hα hβ hGg
  have hE : l = Λ * μ⁻¹ * Λ⁻¹ * μ * Λ⁻¹ * μ⁻¹ * Λ * μ := by rw [hl]; group
  calc l = μ ^ 2 * l * (μ ^ 2)⁻¹ := by rw [← (hc.pow_right 2).eq]; group
    _ = μ ^ 2 * (Λ * μ⁻¹ * Λ⁻¹ * μ * Λ⁻¹ * μ⁻¹ * Λ * μ) * (μ ^ 2)⁻¹ := by rw [← hE]
    _ = _ := by group

/-- The longitude of `Wh⁻₀(T(r, s))` in terms of its meridian and `Λ = pairCompLong` of its
block loops. -/
theorem longitude_pairWhiteheadKnot_eq {r s : ℕ} (h : IsTorusPair r s) :
    longitude (pairWhiteheadKnot r s h) =
      meridian (pairWhiteheadKnot r s h) ^ 2 * pairCompLong r s (pairKLoop h) *
        (meridian (pairWhiteheadKnot r s h))⁻¹ * (pairCompLong r s (pairKLoop h))⁻¹ *
        meridian (pairWhiteheadKnot r s h) *
        ((pairCompLong r s (pairKLoop h))⁻¹ * meridian (pairWhiteheadKnot r s h) *
          pairCompLong r s (pairKLoop h))⁻¹ * (meridian (pairWhiteheadKnot r s h))⁻¹ := by
  have hgap : PairGapRels r s (pairKLoop h) := pairGapRels_of_hom h (MonoidHom.id _)
  obtain ⟨Gg, M, U, hl, hμ, hα, -, hGU, hM⟩ := pairOrbit_split h
  obtain ⟨hH1, hH2⟩ := pairHopf_loops h (pairKGen h)
  have hC : pairKLoop h (pairIdxC r s) * pairKLoop h (pairIdxR r s 0) = 1 := by
    have h0 := hgap.stairLow 0 (Nat.zero_le _)
    simpa [descProd] using h0
  have hR := revWh_clasp _ _ _ _ _ _ hC hgap.top hH1 hH2
  have hcomm := (map_longitude_eq_orbitLoop (pairWhiteheadKnot r s h) (pairBlocks r s) rfl
    (pairBlocks_valid h) (MonoidHom.id _))
  simp only [MonoidHom.id_apply] at hcomm
  have hlm : longitude (pairWhiteheadKnot r s h) * meridian (pairWhiteheadKnot r s h) =
      meridian (pairWhiteheadKnot r s h) * longitude (pairWhiteheadKnot r s h) := by
    rw [hcomm.1]; exact hcomm.2
  exact revWh_algebra _ _ _ _ _ _ _ _ _ _ hl hlm hμ hα hR hH1 hGU hM

/-- The braid relations hold for a tuple fixed by the braid. -/
private theorem revLift_artinRels_of_fixed_reduce {G : Type*} [Group G] (K : BraidKnot)
    (f : Fin K.strands → G) (hf : (braidRun K.strands K.word f).1 = f) :
    ∀ x ∈ artinRels K, FreeGroup.lift f x = 1 := by
  rintro _ ⟨k, rfl⟩
  rw [map_mul, map_inv, FreeGroup.lift_apply_of, map_mul, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one, lift_artinWord_snd, ← braidRun_fst_apply, hf]

/-- Realization from a fixed tuple: a tuple fixed by the run of `pairBlocks r s`, with bottom
entry `a` and companion tuple the images under `ψ` of the generators of `T(r, s)`, gives a
representation of the knot group of `Wh⁻₀(T(r, s))` with meridian `a` and the pattern
longitude. -/
theorem pairRealizes_of_fixedTuple {r s : ℕ} (h : IsTorusPair r s)
    (ψ : KnotGroup (torusPairKnot r s h) →* Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (a : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (f : Fin (pairStrands r s) → Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hfix : runTop (pairStrands r s) (pairBlocks r s) f = f)
    (h0 : f ⟨0, by simp [pairStrands]⟩ = a)
    (hcomp : ∀ k : Fin r, pairCompTuple r s (loopAt (pairStrands r s) (pairBlocks r s) f) k =
      ψ (PresentedGroup.of k)) :
    ∃ ρ : KnotGroup (pairWhiteheadKnot r s h) →* Matrix.SpecialLinearGroup (Fin 2) ℂ,
      ρ (meridian _) = a ∧
        ρ (longitude _) = a ^ 2 * ψ (longitude _) * a⁻¹ * (ψ (longitude _))⁻¹ * a *
          ((ψ (longitude _))⁻¹ * a * ψ (longitude _))⁻¹ * a⁻¹ := by
  let ρ : KnotGroup (pairWhiteheadKnot r s h) →* Matrix.SpecialLinearGroup (Fin 2) ℂ :=
    PresentedGroup.toGroup (f := f) (revLift_artinRels_of_fixed_reduce (pairWhiteheadKnot r s h) f hfix)
  have hρ : ∀ t, ρ (PresentedGroup.of t) = f t := fun t ↦ PresentedGroup.toGroup.of _
  have hgen : (fun t ↦ ρ (pairKGen h t)) = f := funext hρ
  have hloop : ∀ q, ρ (pairKLoop h q) = loopAt (pairStrands r s) (pairBlocks r s) f q := by
    intro q
    rw [pairKLoop, ← loopAt_map, hgen]
  have hcf : ∀ k, ρ (pairCompFun r s (pairKLoop h) k) =
      pairCompFun r s (loopAt (pairStrands r s) (pairBlocks r s) f) k := by
    intro k
    rw [← pairCompFun_map]
    exact congrArg (fun L ↦ pairCompFun r s L k) (funext hloop)
  have hmer : ρ (meridian _) = a := (hρ _).trans h0
  have hΛ : ρ (pairCompLong r s (pairKLoop h)) = ψ (longitude (torusPairKnot r s h)) := by
    rw [longitude_torusPairKnot, pairCompLong, map_mul, map_zpow, map_pow, map_mul, map_zpow,
      map_pow, map_list_prod, List.map_map, torusFullProd, map_list_prod]
    have h1 : ρ (pairCompFun r s (pairKLoop h) 0) = ψ (meridian _) := by
      rw [hcf]
      exact hcomp ⟨0, by have := h.1; omega⟩
    have h2 : ∀ l : List (Fin r), List.map (ρ ∘ pairCompTuple r s (pairKLoop h)) l =
        List.map ψ (List.map (fun j : Fin r ↦
          (PresentedGroup.of j : KnotGroup (torusPairKnot r s h))) l) := by
      intro l
      induction l with
      | nil => rfl
      | cons k l ih =>
        simp only [List.map_cons]
        rw [ih]
        congr 1
        simp only [Function.comp_apply, pairCompTuple]
        rw [hcf]
        exact hcomp k
    rw [h1, h2]
    rfl
  refine ⟨ρ, hmer, ?_⟩
  rw [longitude_pairWhiteheadKnot_eq h]
  simp only [map_mul, map_inv, map_pow, hmer, hΛ]

end AJConjecture
