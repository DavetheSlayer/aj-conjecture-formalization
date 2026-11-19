import Mathlib
import AJFamily.Classical.FamilyPeripheralLongitude
import AJHandoff.TorusKnot.PairKPeriComp
import AJHandoff.TorusKnot.PairKOrbComp
import AJTwist.Classical.TwCVirtual
import AJTwist.Classical.TwCSegments
import AJTwist.Classical.TwCBasePos

/-!
# The orbit loop of a twisted block list (crux of Unit C2)

For a tuple `F` fixed by the run of `twBlocks r s ℓ σ`, with `L = twcLoop r s ℓ σ F` the block
loops at the positions of `pairBlocks r s`, `z_0 = pairCompFun r s L 0` and
`Λ = pairCompLong r s L` (the images of the meridian and the longitude of `T(r, s)` under the
companion homomorphism), the orbit loop of the strand `0` — the image of the longitude — splits
at the two Hopf loops exactly as for the untwisted list (`pairOrbit_split`,
`AJHandoff.TorusKnot.PairKPeriOrbit`), with `Λ` replaced by `Λ z_0^ℓ`:

* negative clasp (`twcOrbit_split_neg`): `λ = G H₁⁻¹ M H₁ U`, `μ = G e_T G⁻¹`,
  `e_(2c) = U μ U⁻¹`, `U⁻¹ R_0 U = z_0`, `G U = Λ z_0^ℓ`, `G R_0⁻¹ M R_0 G⁻¹ = (Λ z_0^ℓ)⁻¹`;
* positive clasp (`twcOrbit_split_pos`): `λ = G H₁ M H₁⁻¹ U`, `e_(2c) = H₁⁻¹ U μ U⁻¹ H₁`, and
  the same three identities.

This is where the twist enters the classical side: `Λ z_0^ℓ` is the image of `λ_C μ_C^ℓ`, the
axis meridian of the paper's gluing (eq. (twistgluing)).

Route.
1. *Orbit.* By `twBlocks_eq_chain_append`, `stPerm_append`, `twChain_detour`, `stPerm_twcBase`
   and `stPerm_pairBlocks_orb`, the orbit of `0` under `stPerm (twBlocks r s ℓ σ)` is the orbit
   `pairOrbT r s` of `pairBlocks r s` with the new strands inserted in two detours: after the
   strand whose bottom position is `j₀` and after the strand whose bottom position is `0`. It
   has `twStrands r s ℓ` elements, and `orbitLoop` is the product over the old orbit of the
   *collapsed* strand loops (a strand loop times the loops of the detour that follows; the
   blocks of the tail collect nothing on the new levels).
2. *Collapsed strand loops.* Split each strand loop with `stLoop_append` into the part in the
   tail and the part in the chain. The tail part is that of the run of `twcBase r s σ` on the
   virtual tuple (`runTop_twcVirtual`, `loopAt_twcVirtual`, `stLoop_resTuple`); the chain part
   is given by `twChain_detour`. With `stLoop_pairBlocks_core` resp. `stLoop_twcBase_pos` for the
   virtual tuple, the collapsed loop of the old position `t` is (Hopf loop) ·
   `twcCore r s ℓ L t`: the loop of the head band on the virtual tuple, which is the last
   factor of the strand loops that contain it, is replaced by the power of `L` of the detour.
3. *Segments.* `G`, `M`, `U` are the products of `twcCore` over the three pieces of the old
   orbit; `twcSeg_GU`, `twcSeg_UG`, `twcSeg_M`, `twcSeg_U` with `pairGapRels_twcLoop`,
   `pairOrb_compFun_zero`, `pairOrb_compLong` give the three identities as in the proof of
   `pairOrbit_split_gen` (`orb_alg_U`, `orb_alg_M` there are private: restate them).
4. *Edges.* `edgeMer_runTop` along the orbit of the fixed tuple gives `μ = G e_T G⁻¹` and the
   formula for `e_(2c)`; closing the orbit shows that the orbit loop commutes with `μ`.

Checked numerically on `SU(2)` representations of the groups of `twBlocks`
(`SCR/C/py/w2_twk_all.py`): `(2,3)` with `ℓ = -1, 1` (negative clasp) and `ℓ = -2, 1` (positive),
`(3,4)` with `ℓ = -1, 2` (negative) and `ℓ = -2, 1` (positive): every identity, and the pattern
relations that follow from them, to `10⁻¹³`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-! ### The head loop in the core loops -/

/-- The loop of the head block is the last factor of the core loops that contain it: changing
the loop at the position `0` multiplies the core loop of `t` on the right, exactly when the
bottom position of `t` is below `j₀`. -/
private theorem pairOrbCore_head_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) {L L' : ℕ → G}
    (hL : ∀ q, 0 < q → q < 2 * pairC r s + 2 → L' q = L q) {t : ℕ}
    (ht : t < pairStrands r s) :
    pairOrbCore r s L' t = pairOrbCore r s L t *
      (if pairOrbPerm r s t < twHeadTop r s then (L 0)⁻¹ * L' 0 else 1) := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  have h2 : 3 ≤ r ∨ pairC r s = s := by
    rcases Nat.lt_or_ge 2 r with h3 | h3
    · exact Or.inl h3
    · obtain rfl : r = 2 := by omega
      right
      simp [pairC]
  set X := (L 0)⁻¹ * L' 0 with hX
  have hA0 : ∀ k, k ≤ 2 * pairC r s + 2 →
      descProd L' 0 k = descProd L 0 k * (if 0 < k then X else 1) := by
    intro k hk
    induction k with
    | zero => rw [descProd_zero_orb, descProd_zero_orb, ite_eq_right (lt_irrefl 0), mul_one]
    | succ k ih =>
      rw [descProd_succ_orb, descProd_succ_orb, ih (by omega), ite_eq_left (Nat.succ_pos k)]
      by_cases hk0 : 0 < k
      · rw [ite_eq_left hk0, hL (0 + k) (by omega) (by omega), mul_assoc]
      · obtain rfl : k = 0 := by omega
        rw [ite_eq_right hk0, mul_one, descProd_zero_orb, hX]
        simp only [Nat.add_zero, mul_one, mul_inv_cancel_left]
  have hD : ∀ a n, a + n ≤ r - 2 → descProd (fun j ↦ L' (pairIdxDp r s j)) a n =
      descProd (fun j ↦ L (pairIdxDp r s j)) a n := fun a n han ↦
    descProd_congr_orb _ _ a a n fun i hi ↦ hL _ (by unfold pairIdxDp pairIdxB; omega)
      (by unfold pairIdxDp pairIdxB; omega)
  have hA : ∀ a n, 0 < a → a + n ≤ 2 * pairC r s + 2 → descProd L' a n = descProd L a n :=
    fun a n ha han ↦ descProd_congr_orb _ _ a a n fun i hi ↦ hL _ (by omega) (by omega)
  have hR : ∀ u, u < s → L' (pairIdxR r s u) = L (pairIdxR r s u) := fun u hu ↦
    hL _ (by unfold pairIdxR pairIdxB; split_ifs <;> omega)
      (by unfold pairIdxR pairIdxB; split_ifs <;> omega)
  have hSkip : ∀ ρ, pairOrbSkip r s L' ρ = pairOrbSkip r s L ρ := fun ρ ↦ by
    unfold pairOrbSkip
    refine congrArg List.prod (List.map_congr_left fun u hu ↦ ?_)
    rw [hR u (List.mem_range.1 (List.mem_reverse.1 hu))]
  have hB : L' (pairIdxB r s) = L (pairIdxB r s) :=
    hL _ (by unfold pairIdxB; omega) (by unfold pairIdxB; omega)
  have hC : L' (pairIdxC r s) = L (pairIdxC r s) :=
    hL _ (by unfold pairIdxC pairIdxB; omega) (by unfold pairIdxC pairIdxB; omega)
  have hH : L' (pairIdxH1 r s) = L (pairIdxH1 r s) :=
    hL _ (by unfold pairIdxH1 pairIdxB; omega) (by unfold pairIdxH1 pairIdxB; omega)
  have hSuf : ∀ j, j < r →
      pairOrbSuf r s L' j = pairOrbSuf r s L j * (if j + 2 ≤ r then X else 1) := fun j hj ↦ by
    unfold pairOrbSuf
    split_ifs with h1 h3 h4 h5
    · rw [hA0 _ (by omega), ite_eq_left (Nat.succ_pos j)]
    · omega
    · rw [hB, hA (r - 2 + pairRunDown r s) (pairRunUp r s) (by omega)
        (by unfold pairRunUp; omega)]
      rcases Nat.lt_or_ge 2 r with h6 | h6
      · rw [hL (r - 2) (by omega) (by omega), hA0 _ (by omega), ite_eq_left (by omega)]
        simp only [mul_assoc]
      · rw [show r - 2 = 0 by omega, descProd_zero_orb, descProd_zero_orb, hX]
        group
    · omega
    · omega
    · rw [mul_one]
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (if pairOrbPerm r s t < twHeadTop r s then X else 1) := ⟨_, rfl⟩
  rw [← hY]
  unfold pairOrbCore
  split_ifs with h1 h3 h4 h5 h6 h7 h8
  · have hi : pairOrbLow r s t < r := by unfold pairOrbLow; split_ifs <;> omega
    have hj : pairOrbNext r s (pairOrbLow r s t) < r := Nat.mod_lt _ (by omega)
    have hc : pairOrbPerm r s t < twHeadTop r s ↔
        pairOrbNext r s (pairOrbLow r s t) + 2 ≤ r := by
      unfold pairOrbPerm twHeadTop pairTop
      rw [ite_eq_left h1]
      generalize pairOrbNext r s (pairOrbLow r s t) = j at hj ⊢
      split_ifs <;> omega
    unfold pairOrbSlotLoop
    rw [hY, if_congr hc rfl rfl, hSkip, hSuf _ hj, hC]
    by_cases hi1 : pairOrbLow r s t + 1 = r
    · rw [ite_eq_left hi1, ite_eq_left hi1]
      simp only [mul_assoc]
    · rw [ite_eq_right hi1, ite_eq_right hi1, hD _ _ (by omega)]
      simp only [mul_assoc]
  · have hc : pairOrbPerm r s t < twHeadTop r s ↔ 0 < r - 2 := by
      unfold pairOrbPerm twHeadTop pairTop
      split_ifs <;> omega
    rw [hY, if_congr hc rfl rfl, hD 0 (r - 2) (by omega), hR (s - 1) (by omega),
      hL (pairIdxRun r s t) (by unfold pairIdxRun; split_ifs <;> omega)
        (by unfold pairIdxRun; split_ifs <;> omega), hA0 _ (by omega)]
    simp only [mul_assoc]
  · have hc : pairOrbPerm r s t < twHeadTop r s ↔ 0 < r - 2 := by
      unfold pairOrbPerm twHeadTop pairTop
      split_ifs <;> omega
    rw [hY, if_congr hc rfl rfl, hD 0 (r - 2) (by omega), hR (s - 1) (by omega),
      hA0 _ (by omega)]
    simp only [mul_assoc]
  · have hc : pairOrbPerm r s t < twHeadTop r s ↔ 0 < r - 2 - pairOrbFoot r s t := by
      unfold pairOrbPerm twHeadTop pairTop pairOrbFoot
      split_ifs <;> omega
    rw [hY, if_congr hc rfl rfl, hD _ _ (by unfold pairOrbFoot; omega), hA0 _ (by omega)]
    simp only [mul_assoc]
  · have hc : ¬ pairOrbPerm r s t < twHeadTop r s := by
      unfold pairOrbPerm twHeadTop pairTop
      split_ifs <;> omega
    rw [hY, ite_eq_right hc, mul_one, hH]
  · have hc : pairOrbPerm r s t < twHeadTop r s ↔ 0 < r - 2 := by
      unfold pairOrbPerm twHeadTop pairTop
      split_ifs <;> omega
    rw [hY, if_congr hc rfl rfl, hC, hR (s - 1) (by omega), hA0 _ (by omega)]
    simp only [mul_assoc]
  · have hc : pairOrbPerm r s t < twHeadTop r s ↔ 0 < r - 2 := by
      unfold pairOrbPerm twHeadTop pairTop
      split_ifs <;> omega
    rw [hY, if_congr hc rfl rfl, hC, hR _ (by unfold pairTop; omega), hB, hA0 _ (by omega)]
    simp only [mul_assoc]
  · have hc : pairOrbPerm r s t < twHeadTop r s ↔ 0 < r - 2 := by
      unfold pairOrbPerm twHeadTop pairTop
      split_ifs <;> omega
    rw [hY, if_congr hc rfl rfl, hR 0 (by omega), hB, hA0 _ (by omega)]
    simp only [mul_assoc]

/-! ### Products along an orbit -/

/-- The product of `S` along the first `n` points of the orbit of `x` under `P`. -/
private def orbProd_twCOrbitSplit (P : ℕ → ℕ) (S : ℕ → G) (n x : ℕ) : G :=
  ((List.range n).map fun j ↦ S (P^[j] x)).prod

/-- Splitting off the last factor of an orbit product. -/
private theorem orbProd_succ_twCOrbitSplit (P : ℕ → ℕ) (S : ℕ → G) (n x : ℕ) :
    orbProd_twCOrbitSplit P S (n + 1) x = orbProd_twCOrbitSplit P S n x * S (P^[n] x) := by
  simp only [orbProd_twCOrbitSplit, List.range_succ, List.map_append, List.prod_append,
    List.map_singleton, List.prod_singleton]

/-- An orbit product of `a + b` steps is the product of `a` steps and of `b` further steps. -/
private theorem orbProd_add_twCOrbitSplit (P : ℕ → ℕ) (S : ℕ → G) (a b x : ℕ) :
    orbProd_twCOrbitSplit P S (a + b) x =
      orbProd_twCOrbitSplit P S a x * orbProd_twCOrbitSplit P S b (P^[a] x) := by
  induction b with
  | zero => simp [orbProd_twCOrbitSplit]
  | succ b ih =>
    rw [← Nat.add_assoc, orbProd_succ_twCOrbitSplit, ih, orbProd_succ_twCOrbitSplit, mul_assoc,
      ← Function.iterate_add_apply, Nat.add_comm b a]

/-- Edge relations along an orbit: if `e t = S t * e (P t) * (S t)⁻¹` on a set of positions
stable under `P`, the value of `e` after `n` steps is the conjugate by the orbit product. -/
private theorem orbProd_edge_twCOrbitSplit (P : ℕ → ℕ) (S e : ℕ → G) (I : ℕ → Prop)
    (hI : ∀ t, I t → I (P t)) (he : ∀ t, I t → e t = S t * e (P t) * (S t)⁻¹) (x : ℕ)
    (hx : I x) (n : ℕ) :
    I (P^[n] x) ∧ e (P^[n] x) =
      (orbProd_twCOrbitSplit P S n x)⁻¹ * e x * orbProd_twCOrbitSplit P S n x := by
  induction n with
  | zero => exact ⟨hx, by simp [orbProd_twCOrbitSplit]⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨by rw [Function.iterate_succ_apply']; exact hI _ h1, ?_⟩
    have h3 := he _ h1
    rw [Function.iterate_succ_apply', orbProd_succ_twCOrbitSplit,
      show e (P (P^[n] x)) = (S (P^[n] x))⁻¹ * e (P^[n] x) * S (P^[n] x) by rw [h3]; group, h2]
    group

/-- A detour: from `t` the map `P'` goes to `Xp a` and then follows `Xp` through positions
`≥ M`, where `P'` and `S'` agree with `Xp` and `XS`. -/
private theorem orbProd_detour_twCOrbitSplit (P' Xp : ℕ → ℕ) (S' XS : ℕ → G) (M : ℕ)
    (hP : ∀ p, M ≤ p → P' p = Xp p) (hS : ∀ p, M ≤ p → S' p = XS p) (t a : ℕ) (Y : G)
    (hPt : P' t = Xp a) (hSt : S' t = Y * XS a) (k : ℕ)
    (hnew : ∀ i, 0 < i → i < k + 1 → M ≤ Xp^[i] a) :
    P'^[k + 1] t = Xp^[k + 1] a ∧
      orbProd_twCOrbitSplit P' S' (k + 1) t =
        Y * ((List.range (k + 1)).map fun i ↦ XS (Xp^[i] a)).prod := by
  induction k with
  | zero =>
    refine ⟨by simpa using hPt, ?_⟩
    simp [orbProd_twCOrbitSplit, hSt]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi hi' ↦ hnew i hi (by omega)
    have hk := hnew (k + 1) (Nat.succ_pos k) (Nat.lt_succ_self _)
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply', h1, hP _ hk, ← Function.iterate_succ_apply' Xp]
    · rw [orbProd_succ_twCOrbitSplit, h2, h1, hS _ hk, List.range_succ (n := k + 1),
        List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_assoc]

/-- The product of `c` over the indices `a, …, b - 1`. -/
private def segProd_twCOrbitSplit (c : ℕ → G) (a b : ℕ) : G :=
  ((List.range (b - a)).map fun k ↦ c (a + k)).prod

/-- The empty segment. -/
private theorem segProd_self_twCOrbitSplit (c : ℕ → G) (a : ℕ) :
    segProd_twCOrbitSplit c a a = 1 := by
  simp [segProd_twCOrbitSplit]

/-- Splitting off the last factor of a segment. -/
private theorem segProd_succ_twCOrbitSplit (c : ℕ → G) {a b : ℕ} (hab : a ≤ b) :
    segProd_twCOrbitSplit c a (b + 1) = segProd_twCOrbitSplit c a b * c b := by
  rw [segProd_twCOrbitSplit, show b + 1 - a = b - a + 1 by omega, List.range_succ,
    List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
    show a + (b - a) = b by omega]
  rfl

/-- A segment is the product of its two parts. -/
private theorem segProd_split_twCOrbitSplit (c : ℕ → G) {a b d : ℕ} (hab : a ≤ b)
    (hbd : b ≤ d) :
    segProd_twCOrbitSplit c a d = segProd_twCOrbitSplit c a b * segProd_twCOrbitSplit c b d := by
  induction d, hbd using Nat.le_induction with
  | base => rw [segProd_self_twCOrbitSplit, mul_one]
  | succ d hbd ih =>
    rw [segProd_succ_twCOrbitSplit c (hab.trans hbd), ih, segProd_succ_twCOrbitSplit c hbd,
      mul_assoc]

/-- Splitting off the first factor of a segment. -/
private theorem segProd_first_twCOrbitSplit (c : ℕ → G) {a b : ℕ} (hab : a < b) :
    segProd_twCOrbitSplit c a b = c a * segProd_twCOrbitSplit c (a + 1) b := by
  rw [segProd_split_twCOrbitSplit c (Nat.le_succ a) hab,
    segProd_succ_twCOrbitSplit c le_rfl, segProd_self_twCOrbitSplit, one_mul]

/-- Segments with the same factors agree. -/
private theorem segProd_congr_twCOrbitSplit (c c' : ℕ → G) {a b : ℕ}
    (hc : ∀ k, a ≤ k → k < b → c k = c' k) :
    segProd_twCOrbitSplit c a b = segProd_twCOrbitSplit c' a b := by
  refine congrArg List.prod (List.map_congr_left fun k hk ↦ hc _ (by omega) ?_)
  have := List.mem_range.1 hk
  omega

/-- Collapsing detours: if from the `k`-th point `T k` of an orbit the map `P'` reaches
`T (k + 1)` after `d k` steps with product `c k`, the orbit of `T 0` under `P'` passes through
the points `T k`, with the products of `c`. -/
private theorem orbProd_collapse_twCOrbitSplit (P' : ℕ → ℕ) (S' : ℕ → G) (T d : ℕ → ℕ)
    (c : ℕ → G) (n : ℕ)
    (hd : ∀ k, k < n → P'^[d k] (T k) = T (k + 1) ∧
      orbProd_twCOrbitSplit P' S' (d k) (T k) = c k) (k : ℕ) (hk : k ≤ n) :
    P'^[∑ i ∈ Finset.range k, d i] (T 0) = T k ∧
      orbProd_twCOrbitSplit P' S' (∑ i ∈ Finset.range k, d i) (T 0) =
        segProd_twCOrbitSplit c 0 k := by
  induction k with
  | zero => simp [orbProd_twCOrbitSplit, segProd_twCOrbitSplit]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨h3, h4⟩ := hd k (by omega)
    rw [Finset.sum_range_succ]
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm _ (d k), Function.iterate_add_apply, h1, h3]
    · rw [orbProd_add_twCOrbitSplit, h1, h2, h4, segProd_succ_twCOrbitSplit c (Nat.zero_le k)]

/-! ### The chain, the tail and the virtual tuple -/

/-- Blocks on the first `n` strands fix the positions `≥ n`. -/
private theorem stPerm_of_ge_twCOrbitSplit {n : ℕ} (bs : List SBlock) (hv : ∀ b ∈ bs, b.Valid n)
    {t : ℕ} (ht : n ≤ t) : stPerm bs t = t := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [stPerm, ih hv.2]
    have hb := hv.1
    cases b <;> simp only [SBlock.Valid, SBlock.perm] at hb ⊢ <;> split_ifs <;> omega

/-- Blocks on the first `n` strands collect nothing at the positions `≥ n`. -/
private theorem stLoop_of_ge_twCOrbitSplit {m n : ℕ} (bs : List SBlock)
    (hv : ∀ b ∈ bs, b.Valid n) (f : Fin m → G) {t : ℕ} (ht : n ≤ t) : stLoop m bs f t = 1 := by
  induction bs generalizing f with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [stLoop, ih hv.2, stPerm_of_ge_twCOrbitSplit bs hv.2 ht, one_mul, SBlock.strandLoop]
    have hb := hv.1
    have hc : b.carries t = false := by
      cases b <;> simp only [SBlock.Valid, SBlock.carries, decide_eq_false_iff_not] at hb ⊢ <;>
        omega
    rw [hc]
    rfl

/-- A tuple is determined by its chamber products. -/
private theorem ext_of_prePr_twCOrbitSplit {m : ℕ} (f f' : Fin m → G)
    (hP : ∀ n, n ≤ m → prePr f n = prePr f' n) : f = f' := by
  funext k
  have h1 := prePr_succ f k k.2
  rw [hP _ k.2, hP _ k.2.le, prePr_succ f' k k.2] at h1
  exact (mul_left_cancel h1).symm

/-- The first `twExtra ℓ + 1` blocks of the twisted list are the chain. -/
private theorem take_twBlocks_twCOrbitSplit (r s : ℕ) (ℓ : ℤ) (σ : Bool) :
    (twBlocks r s ℓ σ).take (twExtra ℓ + 1) = twChain (pairStrands r s) (twHeadTop r s) ℓ := by
  rw [twBlocks_eq_chain_append, ← length_twChain (pairStrands r s) (twHeadTop r s) ℓ,
    List.take_left]

/-- The blocks of the tail of the base list live on the old strands. -/
private theorem twcBase_tail_valid_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) :
    ∀ b ∈ (twcBase r s σ).tail, b.Valid (pairStrands r s) := fun b hb ↦
  twcBase_valid h σ b (List.mem_of_mem_tail hb)

/-- The chain of a fixed tuple restores the new entries. -/
private theorem runTop_twChain_new_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (σ : Bool) (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F)
    (k : Fin (twStrands r s ℓ)) (hk : pairStrands r s ≤ (k : ℕ)) :
    runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F k = F k := by
  have h1 := runTop_apply_of_ge (Nat.le_add_right (pairStrands r s) (twExtra ℓ))
    (twcBase r s σ).tail (twcBase_tail_valid_twCOrbitSplit h σ)
    (runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F) k hk
  rw [← h1]
  conv_rhs => rw [← hF, twBlocks_eq_chain_append, runTop_append]
  rfl

/-- The loop at the head position is the loop of the chain. -/
private theorem twcLoop_zero_twCOrbitSplit (r s : ℕ) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G) :
    twcLoop r s ℓ σ F 0 = twcChainLoop (pairStrands r s) (twHeadTop r s) ℓ F := by
  rw [twcLoop, ite_eq_left rfl, take_twBlocks_twCOrbitSplit]
  rfl

/-- The head band on the virtual tuple gives the restriction of the tuple above the chain. -/
private theorem step_twcVirtual_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F) :
    (SBlock.band 0 (twHeadTop r s)).step (pairStrands r s) (twcVirtual r s ℓ σ F) =
      resTuple (pairStrands_le_twStrands r s ℓ)
        (runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F) := by
  obtain ⟨hj, hjM⟩ := twHeadTop_pos_lt h
  refine ext_of_prePr_twCOrbitSplit _ _ fun n hn ↦ ?_
  have hch : prePr (runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F) n =
      if 1 ≤ n ∧ n ≤ twHeadTop r s then twcLoop r s ℓ σ F 0 * prePr F n else prePr F n := by
    rw [twcLoop_zero_twCOrbitSplit]
    exact prePr_runTop_twChain hj hjM ℓ F (runTop_twChain_new_twCOrbitSplit h ℓ σ F hF) hn
  rw [prePr_resTuple _ _ hn, hch, SBlock.prePr_step _ (show (SBlock.band 0 (twHeadTop r s)).Valid
    (pairStrands r s) from ⟨hj, hjM⟩), prePr_twcVirtual r s ℓ σ F hn]
  simp only [SBlock.gapLoop, SBlock.lo, SBlock.hi, zero_add]
  by_cases hc : 1 ≤ n ∧ n ≤ twHeadTop r s
  · rw [ite_eq_left hc, ite_eq_left hc, SBlock.loop, prePr_twcVirtual r s ℓ σ F (by omega),
      prePr_twcVirtual r s ℓ σ F (by omega), prePr_twcVirtual r s ℓ σ F (Nat.zero_le _),
      prePr_twcVirtual r s ℓ σ F (by omega)]
    simp only [twcVirtCh]
    rw [ite_eq_left hc, ite_eq_right (show ¬(1 ≤ twHeadTop r s + 1 ∧
      twHeadTop r s + 1 ≤ twHeadTop r s) by omega), ite_eq_left (show 1 ≤ twHeadTop r s ∧
      twHeadTop r s ≤ twHeadTop r s by omega), ite_eq_right (show ¬(1 ≤ 0 ∧
      0 ≤ twHeadTop r s) by omega), ite_eq_left (show 1 ≤ 0 + 1 ∧ 0 + 1 ≤ twHeadTop r s by omega),
      edgeMer, prePr_zero]
    group
  · rw [ite_eq_right hc, ite_eq_right hc, one_mul, twcVirtCh, ite_eq_right hc]

/-- The loop collected in the chain by the strand, or by the detour, that enters it at the old
position `q`. -/
private def twcDetourLoop_twCOrbitSplit (r s : ℕ) (ℓ : ℤ) (L0 : G) (q : ℕ) : G :=
  if q = twHeadTop r s then L0 ^ (1 - ℓ) else if q = 0 then L0 ^ ℓ
  else if q < twHeadTop r s then L0 else 1

/-- The collapsed strand loop of the old position `t`: the loop collected in the tail, times the
loop collected in the chain by the strand and the detour through the new positions. -/
private def twcColl_twCOrbitSplit (r s : ℕ) (ℓ : ℤ) (σ : Bool) (F : Fin (twStrands r s ℓ) → G)
    (t : ℕ) : G :=
  stLoop (twStrands r s ℓ) (twcBase r s σ).tail
      (runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F) t *
    twcDetourLoop_twCOrbitSplit r s ℓ (twcLoop r s ℓ σ F 0) (stPerm (twcBase r s σ).tail t)

/-- The strand map of `pairBlocks r s` through the tail of the base list. -/
private theorem stPerm_pairBlocks_tail_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (σ : Bool)
    (t : ℕ) :
    stPerm (pairBlocks r s) t =
      (SBlock.band 0 (twHeadTop r s)).perm (stPerm (twcBase r s σ).tail t) := by
  rw [← stPerm_twcBase r s σ]
  conv_lhs => rw [twcBase_eq_head_cons h σ]
  rfl

/-- The collapsed strand loop through the run of the base list on the virtual tuple. -/
private theorem twcColl_virtual_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F) {t : ℕ}
    (ht : t < pairStrands r s) :
    twcColl_twCOrbitSplit r s ℓ σ F t =
      stLoop (pairStrands r s) (twcBase r s σ) (twcVirtual r s ℓ σ F) t *
        ((if pairOrbPerm r s t < twHeadTop r s then
            (loopAt (pairStrands r s) (twcBase r s σ) (twcVirtual r s ℓ σ F) 0)⁻¹ else 1) *
          twcDetourLoop_twCOrbitSplit r s ℓ (twcLoop r s ℓ σ F 0)
            (stPerm (twcBase r s σ).tail t)) := by
  obtain ⟨hj, hjM⟩ := twHeadTop_pos_lt h
  have hq := stPerm_pairBlocks_tail_twCOrbitSplit h σ t
  rw [stPerm_pairBlocks_orb h ht] at hq
  have hl0 : loopAt (pairStrands r s) (twcBase r s σ) (twcVirtual r s ℓ σ F) 0 =
      (SBlock.band 0 (twHeadTop r s)).loop (twcVirtual r s ℓ σ F) := by
    conv_lhs => rw [twcBase_eq_head_cons h σ]
    simp only [loopAt, List.getD_cons_zero, List.take_zero, runTop_nil]
  have hst : stLoop (pairStrands r s) (twcBase r s σ) (twcVirtual r s ℓ σ F) t =
      stLoop (pairStrands r s) (twcBase r s σ).tail
          ((SBlock.band 0 (twHeadTop r s)).step (pairStrands r s) (twcVirtual r s ℓ σ F)) t *
        (SBlock.band 0 (twHeadTop r s)).strandLoop (twcVirtual r s ℓ σ F)
          (stPerm (twcBase r s σ).tail t) := by
    conv_lhs => rw [twcBase_eq_head_cons h σ]
    rfl
  have hcar : (SBlock.band 0 (twHeadTop r s)).strandLoop (twcVirtual r s ℓ σ F)
      (stPerm (twcBase r s σ).tail t) =
        if pairOrbPerm r s t < twHeadTop r s then
          loopAt (pairStrands r s) (twcBase r s σ) (twcVirtual r s ℓ σ F) 0 else 1 := by
    rw [hl0, hq]
    simp only [SBlock.strandLoop, SBlock.carries, SBlock.perm, decide_eq_true_eq]
    refine if_congr ?_ rfl rfl
    split_ifs <;> omega
  rw [twcColl_twCOrbitSplit, hst, hcar, step_twcVirtual_twCOrbitSplit h ℓ σ F hF,
    ← stLoop_resTuple (pairStrands_le_twStrands r s ℓ) _ (twcBase_tail_valid_twCOrbitSplit h σ)]
  by_cases hc : pairOrbPerm r s t < twHeadTop r s
  · rw [ite_eq_left hc, ite_eq_left hc]
    group
  · rw [ite_eq_right hc, ite_eq_right hc, mul_one, one_mul]

/-- The correction of the head loop and the loop of the detour give the defect. -/
private theorem twcDefect_eq_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (L : ℕ → G)
    {t q : ℕ} (hq : pairOrbPerm r s t = (SBlock.band 0 (twHeadTop r s)).perm q) :
    (if pairOrbPerm r s t < twHeadTop r s then (L 0)⁻¹ else 1) *
        twcDetourLoop_twCOrbitSplit r s ℓ (L 0) q = twcDefect r s ℓ L t := by
  obtain ⟨hj, -⟩ := twHeadTop_pos_lt h
  rw [twcDefect, twcDetourLoop_twCOrbitSplit]
  by_cases h0 : q = 0
  · have hp : pairOrbPerm r s t = twHeadTop r s := by
      rw [hq, h0]
      simp only [SBlock.perm, ite_true]
    rw [hp, h0, ite_eq_right (lt_irrefl _), ite_eq_right hj.ne, ite_eq_left rfl,
      ite_eq_right hj.ne', ite_eq_left rfl, one_mul]
  · by_cases hqj : q = twHeadTop r s
    · have hp : pairOrbPerm r s t = 0 := by
        rw [hq, hqj]
        simp only [SBlock.perm, ite_true, ite_eq_right hj.ne']
      rw [hp, hqj, ite_eq_left hj, ite_eq_left rfl, ite_eq_left rfl, ← zpow_neg_one, ← zpow_add]
      congr 1
      ring
    · have hp : pairOrbPerm r s t = q := by
        rw [hq]
        simp only [SBlock.perm, ite_eq_right h0, ite_eq_right hqj]
      rw [hp, ite_eq_right hqj, ite_eq_right h0, ite_eq_right h0, ite_eq_right hqj]
      by_cases hlt : q < twHeadTop r s
      · rw [ite_eq_left hlt, ite_eq_left hlt, inv_mul_cancel]
      · rw [ite_eq_right hlt, ite_eq_right hlt, one_mul]

/-- The core loop of the virtual run, corrected at the head block, is the twisted core loop of
the loops `twcLoop`. -/
private theorem twcCore_virtual_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F) {t : ℕ}
    (ht : t < pairStrands r s) :
    pairOrbCore r s (loopAt (pairStrands r s) (twcBase r s σ) (twcVirtual r s ℓ σ F)) t *
        ((if pairOrbPerm r s t < twHeadTop r s then
            (loopAt (pairStrands r s) (twcBase r s σ) (twcVirtual r s ℓ σ F) 0)⁻¹ else 1) *
          twcDetourLoop_twCOrbitSplit r s ℓ (twcLoop r s ℓ σ F 0)
            (stPerm (twcBase r s σ).tail t)) =
      twcCore r s ℓ (twcLoop r s ℓ σ F) t := by
  have hnew : ∀ k : Fin (twStrands r s ℓ), pairStrands r s ≤ (k : ℕ) →
      runTop (twStrands r s ℓ) ((twBlocks r s ℓ σ).take (twExtra ℓ + 1)) F k = F k := by
    rw [take_twBlocks_twCOrbitSplit]
    exact runTop_twChain_new_twCOrbitSplit h ℓ σ F hF
  have hLL : ∀ q, 0 < q → q < 2 * pairC r s + 2 →
      loopAt (pairStrands r s) (twcBase r s σ) (twcVirtual r s ℓ σ F) q = twcLoop r s ℓ σ F q :=
    fun q hq hq' ↦ loopAt_twcVirtual h ℓ σ F hnew hq' hq.ne'
  have hq := stPerm_pairBlocks_tail_twCOrbitSplit h σ t
  rw [stPerm_pairBlocks_orb h ht] at hq
  rw [pairOrbCore_head_twCOrbitSplit h hLL ht, twcCore,
    ← twcDefect_eq_twCOrbitSplit h ℓ (twcLoop r s ℓ σ F) hq]
  by_cases hc : pairOrbPerm r s t < twHeadTop r s
  · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hc]
    group
  · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc, mul_one]

/-- The first Hopf loop is the twisted core loop of the strand `pairOrbH1`. -/
private theorem twcCore_H1_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (L : ℕ → G) :
    twcCore r s ℓ L (pairOrbH1 r s) = L (pairIdxH1 r s) ∧
      twcDefect r s ℓ L (pairOrbH1 r s) = 1 := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  obtain ⟨hj, hjM⟩ := twHeadTop_pos_lt h
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  have hP : pairOrbPerm r s (pairOrbH1 r s) = 2 * pairC r s := by
    unfold pairOrbPerm pairOrbH1
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega)]
  have hd : twcDefect r s ℓ L (pairOrbH1 r s) = 1 := by
    have hjT : twHeadTop r s < 2 * pairC r s := by
      unfold twHeadTop pairTop
      split_ifs <;> omega
    rw [twcDefect, hP, ite_eq_right (by omega), ite_eq_right (by omega)]
  refine ⟨?_, hd⟩
  rw [twcCore, hd, mul_one]
  unfold pairOrbCore pairOrbH1
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The collapsed strand loops of a twisted negative-clasp list. -/
private theorem twcColl_neg_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ true) F = F) {t : ℕ}
    (ht : t < pairStrands r s) :
    twcColl_twCOrbitSplit r s ℓ true F t =
      (if t = pairTop r s then twcLoop r s ℓ true F (pairIdxH2 r s) else 1) *
        twcCore r s ℓ (twcLoop r s ℓ true F) t := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hnew : ∀ k : Fin (twStrands r s ℓ), pairStrands r s ≤ (k : ℕ) →
      runTop (twStrands r s ℓ) ((twBlocks r s ℓ true).take (twExtra ℓ + 1)) F k = F k := by
    rw [take_twBlocks_twCOrbitSplit]
    exact runTop_twChain_new_twCOrbitSplit h ℓ true F hF
  have hH2 := loopAt_twcVirtual h ℓ true F hnew (q := pairIdxH2 r s)
    (by unfold pairIdxH2; omega) (by unfold pairIdxH2; omega)
  have hc := stLoop_pairBlocks_core h (twcVirtual r s ℓ true F) ht
  rw [← twcBase_true r s] at hc
  rw [twcColl_virtual_twCOrbitSplit h ℓ true F hF ht, hc, mul_assoc,
    twcCore_virtual_twCOrbitSplit h ℓ true F hF ht, hH2]

/-- The collapsed strand loops of a twisted positive-clasp list. -/
private theorem twcColl_pos_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ false) F = F) {t : ℕ}
    (ht : t < pairStrands r s) :
    twcColl_twCOrbitSplit r s ℓ false F t =
      (if t = pairTop r s then twcLoop r s ℓ false F (pairIdxH1 r s)
        else if t = 2 * pairC r s then twcLoop r s ℓ false F (pairIdxH2 r s) else 1) *
        (if t = pairOrbH1 r s then 1 else twcCore r s ℓ (twcLoop r s ℓ false F) t) := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  obtain ⟨hj, hjM⟩ := twHeadTop_pos_lt h
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  have hnew : ∀ k : Fin (twStrands r s ℓ), pairStrands r s ≤ (k : ℕ) →
      runTop (twStrands r s ℓ) ((twBlocks r s ℓ false).take (twExtra ℓ + 1)) F k = F k := by
    rw [take_twBlocks_twCOrbitSplit]
    exact runTop_twChain_new_twCOrbitSplit h ℓ false F hF
  have hH1 := loopAt_twcVirtual h ℓ false F hnew (q := pairIdxH1 r s)
    (by unfold pairIdxH1 pairIdxB; omega) (by unfold pairIdxH1 pairIdxB; omega)
  have hH2 := loopAt_twcVirtual h ℓ false F hnew (q := pairIdxH2 r s)
    (by unfold pairIdxH2; omega) (by unfold pairIdxH2; omega)
  rw [twcColl_virtual_twCOrbitSplit h ℓ false F hF ht,
    stLoop_twcBase_pos h (twcVirtual r s ℓ false F) ht, hH1, hH2]
  by_cases hH : t = pairOrbH1 r s
  · have hq := stPerm_pairBlocks_tail_twCOrbitSplit h false t
    rw [stPerm_pairBlocks_orb h ht] at hq
    have hd := twcDefect_eq_twCOrbitSplit h ℓ (twcLoop r s ℓ false F) hq
    have hP : ¬ pairOrbPerm r s t < twHeadTop r s := by
      have : pairOrbPerm r s t = 2 * pairC r s := by
        rw [hH]
        unfold pairOrbPerm pairOrbH1
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left (by omega)]
      omega
    rw [ite_eq_right hP, one_mul] at hd
    rw [ite_eq_left hH, ite_eq_left hH, ite_eq_right hP, one_mul, hd, hH,
      (twcCore_H1_twCOrbitSplit h ℓ _).2]
    simp only [mul_one]
  · rw [ite_eq_right hH, ite_eq_right hH, mul_assoc,
      twcCore_virtual_twCOrbitSplit h ℓ false F hF ht]

/-! ### The orbit of the twisted list -/

/-- One step of the old orbit, followed in the twisted list: from the old position `t` the
twisted strand map reaches the next position of the orbit of `pairBlocks r s` after a detour
through new positions, and collects the collapsed strand loop. -/
private theorem twcOrbit_step_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F) :
    ∃ k₁ k₂ : ℕ, 0 < k₁ ∧ 0 < k₂ ∧ k₁ + k₂ = twExtra ℓ + 2 ∧ ∀ t, t < pairStrands r s →
      (stPerm (twBlocks r s ℓ σ))^[if stPerm (twcBase r s σ).tail t = twHeadTop r s then k₁
          else if stPerm (twcBase r s σ).tail t = 0 then k₂ else 1] t =
          stPerm (pairBlocks r s) t ∧
        orbProd_twCOrbitSplit (stPerm (twBlocks r s ℓ σ))
            (stLoop (twStrands r s ℓ) (twBlocks r s ℓ σ) F)
            (if stPerm (twcBase r s σ).tail t = twHeadTop r s then k₁
              else if stPerm (twcBase r s σ).tail t = 0 then k₂ else 1) t =
          twcColl_twCOrbitSplit r s ℓ σ F t := by
  obtain ⟨hj, hjM⟩ := twHeadTop_pos_lt h
  have hfix := runTop_twChain_new_twCOrbitSplit h ℓ σ F hF
  obtain ⟨hold, k₁, k₂, hk1, hk2, hsum, hend1, hnew1, hprod1, hend2, hnew2, hprod2, -⟩ :=
    twChain_detour hj hjM ℓ F hfix
  rw [← twcLoop_zero_twCOrbitSplit r s ℓ σ F] at hold hprod1 hprod2
  replace hold : ∀ t, t < pairStrands r s → t ≠ 0 → t ≠ twHeadTop r s →
      stPerm (twChain (pairStrands r s) (twHeadTop r s) ℓ) t = t ∧
        stLoop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F t =
          if t < twHeadTop r s then twcLoop r s ℓ σ F 0 else 1 := hold
  replace hprod1 : ((List.range k₁).map fun i ↦ stLoop (twStrands r s ℓ)
      (twChain (pairStrands r s) (twHeadTop r s) ℓ) F
      ((stPerm (twChain (pairStrands r s) (twHeadTop r s) ℓ))^[i] (twHeadTop r s))).prod =
        twcLoop r s ℓ σ F 0 ^ (1 - ℓ) := hprod1
  replace hprod2 : ((List.range k₂).map fun i ↦ stLoop (twStrands r s ℓ)
      (twChain (pairStrands r s) (twHeadTop r s) ℓ) F
      ((stPerm (twChain (pairStrands r s) (twHeadTop r s) ℓ))^[i] 0)).prod =
        twcLoop r s ℓ σ F 0 ^ ℓ := hprod2
  have htlv := twcBase_tail_valid_twCOrbitSplit h σ
  have hP : ∀ t, stPerm (twBlocks r s ℓ σ) t =
      stPerm (twChain (pairStrands r s) (twHeadTop r s) ℓ) (stPerm (twcBase r s σ).tail t) :=
    fun t ↦ by rw [twBlocks_eq_chain_append, stPerm_append]
  have hS : ∀ t, stLoop (twStrands r s ℓ) (twBlocks r s ℓ σ) F t =
      stLoop (twStrands r s ℓ) (twcBase r s σ).tail
          (runTop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F) t *
        stLoop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F
          (stPerm (twcBase r s σ).tail t) := fun t ↦ by
    rw [twBlocks_eq_chain_append, stLoop_append]
  have hPnew : ∀ p, pairStrands r s ≤ p → stPerm (twBlocks r s ℓ σ) p =
      stPerm (twChain (pairStrands r s) (twHeadTop r s) ℓ) p := fun p hp ↦ by
    rw [hP, stPerm_of_ge_twCOrbitSplit _ htlv hp]
  have hSnew : ∀ p, pairStrands r s ≤ p → stLoop (twStrands r s ℓ) (twBlocks r s ℓ σ) F p =
      stLoop (twStrands r s ℓ) (twChain (pairStrands r s) (twHeadTop r s) ℓ) F p := fun p hp ↦ by
    rw [hS, stLoop_of_ge_twCOrbitSplit _ htlv _ hp, stPerm_of_ge_twCOrbitSplit _ htlv hp, one_mul]
  refine ⟨k₁, k₂, hk1, hk2, hsum, fun t ht ↦ ?_⟩
  have hT1 := stPerm_pairBlocks_tail_twCOrbitSplit h σ t
  have hqlt : stPerm (twcBase r s σ).tail t < pairStrands r s := stPerm_lt _ htlv _ ht
  rw [hT1, twcColl_twCOrbitSplit, twcDetourLoop_twCOrbitSplit]
  by_cases hqj : stPerm (twcBase r s σ).tail t = twHeadTop r s
  · obtain ⟨k', rfl⟩ : ∃ k', k₁ = k' + 1 := ⟨k₁ - 1, by omega⟩
    obtain ⟨h1, h2⟩ := orbProd_detour_twCOrbitSplit _ _ _ _ _ hPnew hSnew t (twHeadTop r s) _
      (by rw [hP, hqj]) (by rw [hS, hqj]) k' hnew1
    rw [ite_eq_left hqj, ite_eq_left hqj, h1, h2, hend1, hprod1, hqj]
    refine ⟨?_, rfl⟩
    simp only [SBlock.perm, ite_true, ite_eq_right hj.ne']
  · by_cases hq0 : stPerm (twcBase r s σ).tail t = 0
    · obtain ⟨k', rfl⟩ : ∃ k', k₂ = k' + 1 := ⟨k₂ - 1, by omega⟩
      obtain ⟨h1, h2⟩ := orbProd_detour_twCOrbitSplit _ _ _ _ _ hPnew hSnew t 0 _
        (by rw [hP, hq0]) (by rw [hS, hq0]) k' hnew2
      rw [ite_eq_right hqj, ite_eq_left hq0, ite_eq_right hqj, ite_eq_left hq0, h1, h2, hend2,
        hprod2, hq0]
      refine ⟨?_, rfl⟩
      simp only [SBlock.perm, ite_true]
    · obtain ⟨h1, h2⟩ := hold _ hqlt hq0 hqj
      rw [ite_eq_right hqj, ite_eq_right hq0, ite_eq_right hqj, ite_eq_right hq0]
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_one, hP, h1]
        simp only [SBlock.perm, ite_eq_right hq0, ite_eq_right hqj]
      · rw [orbProd_twCOrbitSplit, List.range_one, List.map_singleton, List.prod_singleton,
          Function.iterate_zero, id, hS, h2]

/-- The orbit of `0` of the twisted list passes through the orbit of `pairBlocks r s`, with the
collapsed strand loops, and closes after `twStrands r s ℓ` steps. -/
private theorem twcOrbit_collapse_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (σ : Bool) (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F) :
    ∃ N : ℕ → ℕ, N (pairStrands r s) = twStrands r s ℓ ∧ ∀ k, k ≤ pairStrands r s →
      (stPerm (twBlocks r s ℓ σ))^[N k] 0 = pairOrbT r s k ∧
        orbProd_twCOrbitSplit (stPerm (twBlocks r s ℓ σ))
            (stLoop (twStrands r s ℓ) (twBlocks r s ℓ σ) F) (N k) 0 =
          segProd_twCOrbitSplit (fun i ↦ twcColl_twCOrbitSplit r s ℓ σ F (pairOrbT r s i))
            0 k := by
  obtain ⟨hj, hjM⟩ := twHeadTop_pos_lt h
  obtain ⟨k₁, k₂, hk1, hk2, hsum, hstep⟩ := twcOrbit_step_twCOrbitSplit h ℓ σ F hF
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℕ, ∀ k, d k =
      if stPerm (twcBase r s σ).tail (pairOrbT r s k) = twHeadTop r s then k₁
        else if stPerm (twcBase r s σ).tail (pairOrbT r s k) = 0 then k₂ else 1 :=
    ⟨_, fun _ ↦ rfl⟩
  refine ⟨fun k ↦ ∑ i ∈ Finset.range k, d i, ?_, fun k hk ↦ ?_⟩
  · obtain ⟨hJ1, hJ2⟩ := pairOrbIdx_spec h hjM
    have hT0 : pairOrbT r s 0 = 0 := rfl
    have hM0 : pairOrbT r s (pairStrands r s) = 0 := pairOrbT_strands h
    have hMpos : 0 < pairStrands r s := Nat.succ_pos _
    have hiJ0 : pairOrbIdx r s (twHeadTop r s) ≠ 0 := fun h0 ↦ by
      rw [h0, hT0] at hJ2
      omega
    have hdi : ∀ i, i < pairStrands r s → d i =
        1 + (if i = pairStrands r s - 1 then k₁ - 1 else 0) +
          (if i = pairOrbIdx r s (twHeadTop r s) - 1 then k₂ - 1 else 0) := by
      intro i hi
      have hT1 : pairOrbT r s (i + 1) = (SBlock.band 0 (twHeadTop r s)).perm
          (stPerm (twcBase r s σ).tail (pairOrbT r s i)) := by
        rw [pairOrbT_succ, stPerm_pairBlocks_tail_twCOrbitSplit h σ]
      rw [hd]
      by_cases hqj : stPerm (twcBase r s σ).tail (pairOrbT r s i) = twHeadTop r s
      · have h0 : pairOrbT r s (i + 1) = 0 := by
          rw [hT1, hqj]
          simp only [SBlock.perm, ite_true, ite_eq_right hj.ne']
        have hiM : i + 1 = pairStrands r s := by
          by_contra hne
          have := pairOrbT_injOn h (i := i + 1) (j := 0) (by omega) hMpos h0
          omega
        rw [ite_eq_left hqj, ite_eq_left (by omega), ite_eq_right (by omega)]
        omega
      · by_cases hq0 : stPerm (twcBase r s σ).tail (pairOrbT r s i) = 0
        · have hjj : pairOrbT r s (i + 1) = twHeadTop r s := by
            rw [hT1, hq0]
            simp only [SBlock.perm, ite_true]
          have hiM : i + 1 ≠ pairStrands r s := fun hh ↦ by
            rw [hh, hM0] at hjj
            omega
          have := pairOrbT_injOn h (i := i + 1) (j := pairOrbIdx r s (twHeadTop r s)) (by omega)
            hJ1 (hjj.trans hJ2.symm)
          rw [ite_eq_right hqj, ite_eq_left hq0, ite_eq_right (by omega), ite_eq_left (by omega)]
          omega
        · have hTq : pairOrbT r s (i + 1) = stPerm (twcBase r s σ).tail (pairOrbT r s i) := by
            rw [hT1]
            simp only [SBlock.perm, ite_eq_right hq0, ite_eq_right hqj]
          have h1 : i ≠ pairStrands r s - 1 := fun hh ↦
            hq0 (by rw [← hTq, show i + 1 = pairStrands r s by omega, hM0])
          have h2 : i ≠ pairOrbIdx r s (twHeadTop r s) - 1 := fun hh ↦
            hqj (by rw [← hTq, show i + 1 = pairOrbIdx r s (twHeadTop r s) by omega, hJ2])
          rw [ite_eq_right hqj, ite_eq_right hq0, ite_eq_right h1, ite_eq_right h2]
    show ∑ i ∈ Finset.range (pairStrands r s), d i = twStrands r s ℓ
    rw [Finset.sum_congr rfl fun i hi ↦ hdi i (Finset.mem_range.1 hi), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
      Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left (Finset.mem_range.2 (by omega)),
      ite_eq_left (Finset.mem_range.2 (by omega))]
    unfold twStrands
    omega
  · exact orbProd_collapse_twCOrbitSplit _ _ (pairOrbT r s) d _ (pairStrands r s) (fun k hk ↦ by
      rw [hd, pairOrbT_succ]
      exact hstep _ (pairOrbT_lt h k)) k hk

/-! ### The segments and the companion tuple -/

/-- Conjugation by `y` undone. -/
private theorem unconj_twCOrbitSplit (y x z : G) (hx : y * x * y⁻¹ = z) : x = y⁻¹ * z * y := by
  rw [← hx]
  group

/-- The companion meridian from the bottom piece `U`. -/
private theorem alg_U_twCOrbitSplit (y0 y1 K U : G) (W N : ℤ)
    (hU : y0 * U * y0⁻¹ = K ^ W * y1 ^ N) (hy : y0 = K ^ W * y1 * K ^ (-W)) :
    U⁻¹ * y0 * U = y0⁻¹ * y1 * y0 := by
  have hU' := unconj_twCOrbitSplit y0 U _ hU
  have hk : K ^ (-W) * y0 * K ^ W = y1 := by
    rw [hy]
    group
  calc U⁻¹ * y0 * U = y0⁻¹ * y1 ^ (-N) * (K ^ (-W) * y0 * K ^ W) * y1 ^ N * y0 := by
        rw [hU']
        group
    _ = y0⁻¹ * y1 * y0 := by
        rw [hk]
        group

/-- Conjugating by an element that commutes. -/
private theorem conj_comm_twCOrbitSplit (y X : G) (h : Commute X y) : y⁻¹ * X * y = X := by
  rw [mul_assoc, h.eq, inv_mul_cancel_left]

/-- The final group theory of the orbit split. -/
private theorem alg_M_twCOrbitSplit (y K Gg U M Lam : G) (b : ℤ) (hKy : Commute K y)
    (hUG : y * (U * Gg) * y⁻¹ = K * y ^ (-b)) (hM : y * M * y⁻¹ = K⁻¹ * y ^ b)
    (hLam : Gg * U = Lam) : Gg * y⁻¹ * M * y * Gg⁻¹ = Lam⁻¹ := by
  have hM' : M = K⁻¹ * y ^ b := by
    rw [unconj_twCOrbitSplit y M _ hM]
    exact conj_comm_twCOrbitSplit y _ (hKy.inv_left.mul_left (Commute.zpow_self y b))
  have hUG' : U * Gg = K * y ^ (-b) := by
    rw [unconj_twCOrbitSplit y _ _ hUG]
    exact conj_comm_twCOrbitSplit y _ (hKy.mul_left (Commute.zpow_self y (-b)))
  have h1 : y⁻¹ * M * y = (U * Gg)⁻¹ := by
    rw [conj_comm_twCOrbitSplit y M (by
        rw [hM']
        exact hKy.inv_left.mul_left (Commute.zpow_self y b)),
      hM', hUG', mul_inv_rev, zpow_neg, inv_inv]
    exact ((hKy.zpow_right b).inv_left).eq
  calc Gg * y⁻¹ * M * y * Gg⁻¹ = Gg * (y⁻¹ * M * y) * Gg⁻¹ := by group
    _ = (Gg * U)⁻¹ := by
        rw [h1]
        group
    _ = Lam⁻¹ := by rw [hLam]

/-- The three identities between the twisted segments and the companion tuple, for abstract
loops with the gap relations. -/
private theorem twcSeg_alg_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) {L : ℕ → G}
    (hL : PairGapRels r s L) :
    (twcSeg r s ℓ L (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s))⁻¹ *
          L (pairIdxR r s 0) *
          twcSeg r s ℓ L (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s) =
        pairCompFun r s L 0 ∧
      twcSeg r s ℓ L 0 (pairOrbIdx r s (pairTop r s)) *
          twcSeg r s ℓ L (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s) =
        pairCompLong r s L * pairCompFun r s L 0 ^ ℓ ∧
      twcSeg r s ℓ L 0 (pairOrbIdx r s (pairTop r s)) * (L (pairIdxR r s 0))⁻¹ *
          twcSeg r s ℓ L (pairOrbIdx r s (pairTop r s)) (pairOrbIdx r s (pairOrbH1 r s)) *
          L (pairIdxR r s 0) * (twcSeg r s ℓ L 0 (pairOrbIdx r s (pairTop r s)))⁻¹ =
        (pairCompLong r s L * pairCompFun r s L 0 ^ ℓ)⁻¹ := by
  have hy0 : pairOrbY r s L 0 = L (pairIdxR r s 0) := by
    have := pairOrbY_natCast (r := r) (s := s) L (i := 0) (by have := h.2.1; omega)
    rwa [Nat.cast_zero] at this
  have hz : (pairCompFun r s L 0) ^ ℓ =
      (pairOrbY r s L 0)⁻¹ * pairOrbY r s L 1 ^ ℓ * pairOrbY r s L 0 := by
    rw [pairOrb_compFun_zero h hL]
    have := conj_zpow (a := (pairOrbY r s L 0)⁻¹) (b := pairOrbY r s L 1) (i := ℓ)
    rwa [inv_inv] at this
  have h5 : twcSeg r s ℓ L 0 (pairOrbIdx r s (pairTop r s)) *
      twcSeg r s ℓ L (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s) =
      pairCompLong r s L * pairCompFun r s L 0 ^ ℓ := by
    rw [unconj_twCOrbitSplit _ _ _ (twcSeg_GU h ℓ hL), pairOrb_compLong h hL, hz, zpow_add]
    group
  refine ⟨?_, h5, ?_⟩
  · obtain ⟨W, N, hU, hy⟩ := twcSeg_U h ℓ hL
    rw [pairOrb_compFun_zero h hL, ← hy0]
    exact alg_U_twCOrbitSplit _ _ _ _ W N hU hy
  · have hKy : Commute (pairOrbK r s L ^ (s : ℤ)) (pairOrbY r s L 0) := by
      have hk := pairOrbK_zpow_conj h hL 0 (s : ℤ)
      rw [zero_add, mul_comm (r : ℤ), ← zero_add ((s : ℤ) * r), pairOrbY_add_mul_period] at hk
      exact (mul_inv_eq_iff_eq_mul.1 (by rw [← zpow_neg]; exact hk))
    rw [← hy0]
    refine alg_M_twCOrbitSplit _ _ _ _ _ _ (((r * s : ℕ) : ℤ) - ℓ) hKy ?_ ?_ h5
    · rw [neg_sub, sub_eq_neg_add]
      exact twcSeg_UG h ℓ hL
    · rw [← zpow_neg]
      exact twcSeg_M h ℓ hL

/-! ### The orbit loop and the edge meridians -/

/-- The orbit loop of a fixed tuple of a twisted list is the product of the collapsed strand
loops along the orbit of `pairBlocks r s`; it commutes with the meridian, and the edge
meridians along the orbit are conjugates of the meridian by the partial products. -/
private theorem twcOrbit_edges_twCOrbitSplit {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ σ) F = F) :
    orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ σ) F =
        segProd_twCOrbitSplit (fun i ↦ twcColl_twCOrbitSplit r s ℓ σ F (pairOrbT r s i)) 0
          (pairStrands r s) ∧
      ∀ k, k ≤ pairStrands r s → edgeMer F (pairOrbT r s k) =
        (segProd_twCOrbitSplit (fun i ↦ twcColl_twCOrbitSplit r s ℓ σ F (pairOrbT r s i))
            0 k)⁻¹ * edgeMer F 0 *
          segProd_twCOrbitSplit (fun i ↦ twcColl_twCOrbitSplit r s ℓ σ F (pairOrbT r s i))
            0 k := by
  obtain ⟨N, hN, hk⟩ := twcOrbit_collapse_twCOrbitSplit h ℓ σ F hF
  have hv := twBlocks_valid h ℓ σ
  have hpos : 0 < twStrands r s ℓ := by
    unfold twStrands pairStrands
    omega
  have hedge := fun n ↦ (orbProd_edge_twCOrbitSplit (stPerm (twBlocks r s ℓ σ))
    (stLoop (twStrands r s ℓ) (twBlocks r s ℓ σ) F) (edgeMer F) (fun t ↦ t < twStrands r s ℓ)
    (fun t ht ↦ stPerm_lt _ hv t ht) (fun t ht ↦ by
      have := edgeMer_runTop _ hv F t ht
      rwa [hF] at this) 0 hpos n).2
  refine ⟨?_, fun k hk' ↦ ?_⟩
  · rw [← (hk _ le_rfl).2, hN]
    rfl
  · obtain ⟨h1, h2⟩ := hk k hk'
    have := hedge (N k)
    rwa [h1, h2] at this

/-- From a product that commutes with `μ`. -/
private theorem conj_of_comm_twCOrbitSplit (A B μ : G) (hc : μ = (A * B)⁻¹ * μ * (A * B)) :
    A⁻¹ * μ * A = B * μ * B⁻¹ := by
  have h1 : A⁻¹ * μ * A = B * ((A * B)⁻¹ * μ * (A * B)) * B⁻¹ := by group
  rw [h1, ← hc]

/-- The orbit loop of a twisted negative-clasp block list, cut at the two Hopf loops. -/
theorem twcOrbit_split_neg {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ true) F = F) :
    ∃ Gg M U : G,
      orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ true) F =
          Gg * (twcLoop r s ℓ true F (pairIdxH1 r s))⁻¹ * M *
            twcLoop r s ℓ true F (pairIdxH1 r s) * U ∧
        edgeMer F 0 = Gg * edgeMer F (pairTop r s) * Gg⁻¹ ∧
        edgeMer F (pairTop r s + 1) = U * edgeMer F 0 * U⁻¹ ∧
        U⁻¹ * twcLoop r s ℓ true F (pairIdxR r s 0) * U =
          pairCompFun r s (twcLoop r s ℓ true F) 0 ∧
        Gg * U = pairCompLong r s (twcLoop r s ℓ true F) *
          pairCompFun r s (twcLoop r s ℓ true F) 0 ^ ℓ ∧
        Gg * (twcLoop r s ℓ true F (pairIdxR r s 0))⁻¹ * M *
            twcLoop r s ℓ true F (pairIdxR r s 0) * Gg⁻¹ =
          (pairCompLong r s (twcLoop r s ℓ true F) *
            pairCompFun r s (twcLoop r s ℓ true F) 0 ^ ℓ)⁻¹ := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hL := pairGapRels_twcLoop h ℓ true F hF
  obtain ⟨hlam, hedge⟩ := twcOrbit_edges_twCOrbitSplit h ℓ true F hF
  obtain ⟨h4, h5, h6⟩ := twcSeg_alg_twCOrbitSplit h ℓ hL
  obtain ⟨hiT0, hiTH, hiH, h2c⟩ := pairOrb_idx_order h
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  have hT1 : pairTop r s + 1 = 2 * pairC r s := by
    unfold pairTop
    omega
  obtain ⟨hiTm, hT⟩ := pairOrbIdx_spec h (show pairTop r s < pairStrands r s by omega)
  obtain ⟨hiHm, hH⟩ := pairOrbIdx_spec h (show pairOrbH1 r s < pairStrands r s by
    unfold pairOrbH1
    omega)
  have hc : ∀ k, k < pairStrands r s → k ≠ pairOrbIdx r s (pairTop r s) →
      twcColl_twCOrbitSplit r s ℓ true F (pairOrbT r s k) =
        twcCore r s ℓ (twcLoop r s ℓ true F) (pairOrbT r s k) := fun k hk hne ↦ by
    rw [twcColl_neg_twCOrbitSplit h ℓ F hF (pairOrbT_lt h k),
      ite_eq_right (fun hh ↦ hne (pairOrbT_injOn h hk hiTm (hh.trans hT.symm))), one_mul]
  have hG : segProd_twCOrbitSplit (fun i ↦ twcColl_twCOrbitSplit r s ℓ true F (pairOrbT r s i))
      0 (pairOrbIdx r s (pairTop r s)) =
      twcSeg r s ℓ (twcLoop r s ℓ true F) 0 (pairOrbIdx r s (pairTop r s)) :=
    segProd_congr_twCOrbitSplit _ _ fun k _ hk ↦ hc k (by omega) (by omega)
  have hrest : segProd_twCOrbitSplit
      (fun i ↦ twcColl_twCOrbitSplit r s ℓ true F (pairOrbT r s i))
      (pairOrbIdx r s (pairTop r s)) (pairStrands r s) =
      twcLoop r s ℓ true F (pairIdxH2 r s) *
        twcSeg r s ℓ (twcLoop r s ℓ true F) (pairOrbIdx r s (pairTop r s)) (pairStrands r s) := by
    rw [segProd_first_twCOrbitSplit _ hiTm, twcColl_neg_twCOrbitSplit h ℓ F hF (pairOrbT_lt h _),
      ite_eq_left hT, segProd_congr_twCOrbitSplit _
        (fun k ↦ twcCore r s ℓ (twcLoop r s ℓ true F) (pairOrbT r s k))
        fun k hk1 hk2 ↦ hc k hk2 (by omega), mul_assoc]
    congr 1
    exact (segProd_first_twCOrbitSplit
      (fun k ↦ twcCore r s ℓ (twcLoop r s ℓ true F) (pairOrbT r s k)) hiTm).symm
  have hMU : twcSeg r s ℓ (twcLoop r s ℓ true F) (pairOrbIdx r s (pairTop r s))
      (pairStrands r s) =
      twcSeg r s ℓ (twcLoop r s ℓ true F) (pairOrbIdx r s (pairTop r s))
          (pairOrbIdx r s (pairOrbH1 r s)) * twcLoop r s ℓ true F (pairIdxH1 r s) *
        twcSeg r s ℓ (twcLoop r s ℓ true F) (pairOrbIdx r s (pairOrbH1 r s) + 1)
          (pairStrands r s) := by
    have h1 := segProd_split_twCOrbitSplit
      (fun k ↦ twcCore r s ℓ (twcLoop r s ℓ true F) (pairOrbT r s k)) hiTH.le hiHm.le
    have h2 := segProd_first_twCOrbitSplit
      (fun k ↦ twcCore r s ℓ (twcLoop r s ℓ true F) (pairOrbT r s k)) hiHm
    simp only [hH, (twcCore_H1_twCOrbitSplit h ℓ (twcLoop r s ℓ true F)).1] at h2
    rw [h2, ← mul_assoc] at h1
    exact h1
  have hH2 : twcLoop r s ℓ true F (pairIdxH2 r s) = (twcLoop r s ℓ true F (pairIdxH1 r s))⁻¹ :=
    eq_inv_of_mul_eq_one_left hL.top
  refine ⟨twcSeg r s ℓ (twcLoop r s ℓ true F) 0 (pairOrbIdx r s (pairTop r s)),
    twcSeg r s ℓ (twcLoop r s ℓ true F) (pairOrbIdx r s (pairTop r s))
      (pairOrbIdx r s (pairOrbH1 r s)),
    twcSeg r s ℓ (twcLoop r s ℓ true F) (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s),
    ?_, ?_, ?_, h4, h5, h6⟩
  · rw [hlam, segProd_split_twCOrbitSplit _ (Nat.zero_le _) hiTm.le, hG, hrest, hMU, hH2]
    group
  · have he := hedge _ hiTm.le
    rw [hT, hG] at he
    rw [he]
    group
  · have he := hedge _ hiH.le
    have hcomm := hedge _ le_rfl
    rw [pairOrbT_strands h, segProd_split_twCOrbitSplit _ (Nat.zero_le _) hiH.le,
      segProd_congr_twCOrbitSplit _
        (fun k ↦ twcCore r s ℓ (twcLoop r s ℓ true F) (pairOrbT r s k))
        fun k hk1 hk2 ↦ hc k hk2 (by omega)] at hcomm
    rw [h2c] at he
    rw [hT1, he]
    exact conj_of_comm_twCOrbitSplit _ _ _ hcomm

/-- The orbit loop of a twisted positive-clasp block list, cut at the two Hopf loops. -/
theorem twcOrbit_split_pos {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (F : Fin (twStrands r s ℓ) → G)
    (hF : runTop (twStrands r s ℓ) (twBlocks r s ℓ false) F = F) :
    ∃ Gg M U : G,
      orbitLoop (twStrands r s ℓ) (twBlocks r s ℓ false) F =
          Gg * twcLoop r s ℓ false F (pairIdxH1 r s) * M *
            (twcLoop r s ℓ false F (pairIdxH1 r s))⁻¹ * U ∧
        edgeMer F 0 = Gg * edgeMer F (pairTop r s) * Gg⁻¹ ∧
        edgeMer F (pairTop r s + 1) =
          (twcLoop r s ℓ false F (pairIdxH1 r s))⁻¹ * U * edgeMer F 0 * U⁻¹ *
            twcLoop r s ℓ false F (pairIdxH1 r s) ∧
        U⁻¹ * twcLoop r s ℓ false F (pairIdxR r s 0) * U =
          pairCompFun r s (twcLoop r s ℓ false F) 0 ∧
        Gg * U = pairCompLong r s (twcLoop r s ℓ false F) *
          pairCompFun r s (twcLoop r s ℓ false F) 0 ^ ℓ ∧
        Gg * (twcLoop r s ℓ false F (pairIdxR r s 0))⁻¹ * M *
            twcLoop r s ℓ false F (pairIdxR r s 0) * Gg⁻¹ =
          (pairCompLong r s (twcLoop r s ℓ false F) *
            pairCompFun r s (twcLoop r s ℓ false F) 0 ^ ℓ)⁻¹ := by
  obtain ⟨hr, hrs, hsc, hE⟩ := pairOrb_arith h
  have hL := pairGapRels_twcLoop h ℓ false F hF
  obtain ⟨hlam, hedge⟩ := twcOrbit_edges_twCOrbitSplit h ℓ false F hF
  obtain ⟨h4, h5, h6⟩ := twcSeg_alg_twCOrbitSplit h ℓ hL
  obtain ⟨hiT0, hiTH, hiH, h2c⟩ := pairOrb_idx_order h
  have hm : pairStrands r s = 2 * pairC r s + 1 := rfl
  have hTd : pairTop r s = 2 * pairC r s - 1 := rfl
  have hHd : pairOrbH1 r s = 2 * pairC r s - s - 1 := rfl
  have hT1 : pairTop r s + 1 = 2 * pairC r s := by omega
  obtain ⟨hiTm, hT⟩ := pairOrbIdx_spec h (show pairTop r s < pairStrands r s by omega)
  obtain ⟨hiHm, hH⟩ := pairOrbIdx_spec h (show pairOrbH1 r s < pairStrands r s by omega)
  have hc : ∀ k, k < pairStrands r s → k ≠ pairOrbIdx r s (pairTop r s) →
      k ≠ pairOrbIdx r s (pairOrbH1 r s) → k ≠ pairOrbIdx r s (pairOrbH1 r s) + 1 →
      twcColl_twCOrbitSplit r s ℓ false F (pairOrbT r s k) =
        twcCore r s ℓ (twcLoop r s ℓ false F) (pairOrbT r s k) := fun k hk hne1 hne2 hne3 ↦ by
    rw [twcColl_pos_twCOrbitSplit h ℓ F hF (pairOrbT_lt h k),
      ite_eq_right (fun hh ↦ hne1 (pairOrbT_injOn h hk hiTm (hh.trans hT.symm))),
      ite_eq_right (fun hh ↦ hne3 (pairOrbT_injOn h hk hiH (hh.trans h2c.symm))), one_mul,
      ite_eq_right (fun hh ↦ hne2 (pairOrbT_injOn h hk hiHm (hh.trans hH.symm)))]
  have hG : segProd_twCOrbitSplit (fun i ↦ twcColl_twCOrbitSplit r s ℓ false F (pairOrbT r s i))
      0 (pairOrbIdx r s (pairTop r s)) =
      twcSeg r s ℓ (twcLoop r s ℓ false F) 0 (pairOrbIdx r s (pairTop r s)) :=
    segProd_congr_twCOrbitSplit _ _ fun k _ hk ↦ hc k (by omega) (by omega) (by omega) (by omega)
  have hM : segProd_twCOrbitSplit (fun i ↦ twcColl_twCOrbitSplit r s ℓ false F (pairOrbT r s i))
      (pairOrbIdx r s (pairTop r s)) (pairOrbIdx r s (pairOrbH1 r s)) =
      twcLoop r s ℓ false F (pairIdxH1 r s) *
        twcSeg r s ℓ (twcLoop r s ℓ false F) (pairOrbIdx r s (pairTop r s))
          (pairOrbIdx r s (pairOrbH1 r s)) := by
    rw [segProd_first_twCOrbitSplit _ hiTH, twcColl_pos_twCOrbitSplit h ℓ F hF (pairOrbT_lt h _),
      hT, ite_eq_left rfl, ite_eq_right (by omega), segProd_congr_twCOrbitSplit _
        (fun k ↦ twcCore r s ℓ (twcLoop r s ℓ false F) (pairOrbT r s k))
        fun k hk1 hk2 ↦ hc k (by omega) (by omega) (by omega) (by omega), mul_assoc]
    congr 1
    have h1 := segProd_first_twCOrbitSplit
      (fun k ↦ twcCore r s ℓ (twcLoop r s ℓ false F) (pairOrbT r s k)) hiTH
    simp only [hT] at h1
    exact h1.symm
  have hHH : segProd_twCOrbitSplit
      (fun i ↦ twcColl_twCOrbitSplit r s ℓ false F (pairOrbT r s i))
      (pairOrbIdx r s (pairOrbH1 r s)) (pairOrbIdx r s (pairOrbH1 r s) + 1) = 1 := by
    rw [segProd_first_twCOrbitSplit _ (Nat.lt_succ_self _), segProd_self_twCOrbitSplit, mul_one,
      twcColl_pos_twCOrbitSplit h ℓ F hF (pairOrbT_lt h _), hH, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left rfl, mul_one]
  have hU : segProd_twCOrbitSplit (fun i ↦ twcColl_twCOrbitSplit r s ℓ false F (pairOrbT r s i))
      (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s) =
      twcLoop r s ℓ false F (pairIdxH2 r s) *
        twcSeg r s ℓ (twcLoop r s ℓ false F) (pairOrbIdx r s (pairOrbH1 r s) + 1)
          (pairStrands r s) := by
    rw [segProd_first_twCOrbitSplit _ hiH, twcColl_pos_twCOrbitSplit h ℓ F hF (pairOrbT_lt h _),
      h2c, ite_eq_right (by omega), ite_eq_left rfl, ite_eq_right (by omega),
      segProd_congr_twCOrbitSplit _
        (fun k ↦ twcCore r s ℓ (twcLoop r s ℓ false F) (pairOrbT r s k))
        fun k hk1 hk2 ↦ hc k (by omega) (by omega) (by omega) (by omega), mul_assoc]
    congr 1
    have h1 := segProd_first_twCOrbitSplit
      (fun k ↦ twcCore r s ℓ (twcLoop r s ℓ false F) (pairOrbT r s k)) hiH
    simp only [h2c] at h1
    exact h1.symm
  have hH2 : twcLoop r s ℓ false F (pairIdxH2 r s) =
      (twcLoop r s ℓ false F (pairIdxH1 r s))⁻¹ := eq_inv_of_mul_eq_one_left hL.top
  have hA : segProd_twCOrbitSplit (fun i ↦ twcColl_twCOrbitSplit r s ℓ false F (pairOrbT r s i))
      0 (pairOrbIdx r s (pairOrbH1 r s) + 1) =
      twcSeg r s ℓ (twcLoop r s ℓ false F) 0 (pairOrbIdx r s (pairTop r s)) *
        (twcLoop r s ℓ false F (pairIdxH1 r s) *
          twcSeg r s ℓ (twcLoop r s ℓ false F) (pairOrbIdx r s (pairTop r s))
            (pairOrbIdx r s (pairOrbH1 r s))) := by
    rw [segProd_split_twCOrbitSplit _ (Nat.zero_le _) (show pairOrbIdx r s (pairTop r s) ≤
        pairOrbIdx r s (pairOrbH1 r s) + 1 by omega),
      segProd_split_twCOrbitSplit _ hiTH.le (Nat.le_succ _), hG, hM, hHH, mul_one]
  refine ⟨twcSeg r s ℓ (twcLoop r s ℓ false F) 0 (pairOrbIdx r s (pairTop r s)),
    twcSeg r s ℓ (twcLoop r s ℓ false F) (pairOrbIdx r s (pairTop r s))
      (pairOrbIdx r s (pairOrbH1 r s)),
    twcSeg r s ℓ (twcLoop r s ℓ false F) (pairOrbIdx r s (pairOrbH1 r s) + 1) (pairStrands r s),
    ?_, ?_, ?_, h4, h5, h6⟩
  · rw [hlam, segProd_split_twCOrbitSplit _ (Nat.zero_le _) hiH.le, hA, hU, hH2]
    group
  · have he := hedge _ hiTm.le
    rw [hT, hG] at he
    rw [he]
    group
  · have he := hedge _ hiH.le
    have hcomm := hedge _ le_rfl
    rw [pairOrbT_strands h, segProd_split_twCOrbitSplit _ (Nat.zero_le _) hiH.le,
      hU, hH2] at hcomm
    rw [h2c] at he
    rw [hT1, he, conj_of_comm_twCOrbitSplit _ _ _ hcomm]
    group

end AJConjecture
