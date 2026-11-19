import Mathlib
import AJHandoff.TorusKnot.PairKOrbDefs

/-!
# The block loops of `pairBlocks r s` in terms of the rounds

For block loops `L` satisfying the gap relations (`PairGapRels r s L`), with the rounds
`y_i = R_(i mod s)` (`pairOrbY`) and `K = C⁻¹ A⁻¹ B⁻¹` (`pairOrbK`):

* every `r` consecutive rounds have the product `K` (`pairOrb_window`), so conjugation by `K`
  shifts the rounds by `r` (`pairOrbK_conj`, `pairOrbK_zpow_conj`) and `K ^ s` commutes with them;
* `C = y_0⁻¹`, `A_(n-1) ⋯ A_0 = y_0⁻¹ (y_n ⋯ y_1)⁻¹ y_0`,
  `D'_(r-3) ⋯ D'_(r-2-n) = y_0⁻¹ (y_n ⋯ y_1) y_0` (`n ≤ r - 2`), `B = y_(-1)⁻¹`, and every run
  block is `y_(-1)⁻¹`.

Route: `pairOrb_window` is `pairRoundSeq_window` of `AJHandoff.TorusKnot.PairKPeriComp` (private
there; copy its proof with `wrap_window_identity`) for `p ≥ 0`, extended to `p : ℤ` by
periodicity. `C` is `stairLow 0`; the `A`-prefixes are `stairLow n`; the `D'`-prefixes are `bot n`
with the `A`-prefixes; `B` from the definition of `K`, the window at `p = 0` and the window
relation `y_(r-1) = (y_(r-2) ⋯ y_0) y_(-1) (⋯)⁻¹`; the run blocks from `run` and the `D'`-prefix
`n = r - 2`. Checked exactly in the torus knot group (`AJHandoff.TorusKnot.PairKOrbDefs`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-! ### Descending products -/

/-- The empty descending product. -/
private theorem descProd_zero_rnd (g : ℕ → G) (a : ℕ) : descProd g a 0 = 1 := by
  simp [descProd]

/-- Splitting off the top factor of a descending product. -/
private theorem descProd_succ_top_rnd (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = g (a + n) * descProd g a n := by
  simp [descProd, List.range_succ]

/-- Splitting off the bottom factor of a descending product. -/
private theorem descProd_succ_bot_rnd (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = descProd g (a + 1) n * g a := by
  induction n with
  | zero => simp [descProd]
  | succ n ih =>
    rw [descProd_succ_top_rnd, ih, descProd_succ_top_rnd, mul_assoc,
      show a + 1 + n = a + (n + 1) by omega]

/-- Splitting a descending product into an upper and a lower part. -/
private theorem descProd_add_rnd (g : ℕ → G) (a n k : ℕ) :
    descProd g a (n + k) = descProd g (a + k) n * descProd g a k := by
  induction n with
  | zero => simp [descProd_zero_rnd]
  | succ n ih =>
    rw [show n + 1 + k = n + k + 1 by omega, descProd_succ_top_rnd, ih, descProd_succ_top_rnd,
      mul_assoc, show a + (n + k) = a + k + n by omega]

/-- A descending product of one factor. -/
private theorem descProd_one_rnd (g : ℕ → G) (a : ℕ) : descProd g a 1 = g a := by
  simp [descProd]

/-- Splitting off the bottom factor of a nonempty descending product from `0`. -/
private theorem descProd_split_bot_rnd (g : ℕ → G) {n : ℕ} (hn : 1 ≤ n) :
    descProd g 0 n = descProd g 1 (n - 1) * g 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [descProd_succ_bot_rnd, Nat.add_sub_cancel]

/-- Splitting off the top factor of a nonempty descending product from `0`. -/
private theorem descProd_split_top_rnd (g : ℕ → G) {n : ℕ} (hn : 1 ≤ n) :
    descProd g 0 n = g (n - 1) * descProd g 0 (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [descProd_succ_top_rnd, Nat.add_sub_cancel, Nat.zero_add]

/-- Descending products with the same factors agree. -/
private theorem descProd_congr_rnd (g g' : ℕ → G) (a b n : ℕ)
    (H : ∀ i, i < n → g (a + i) = g' (b + i)) : descProd g a n = descProd g' b n := by
  induction n with
  | zero => simp [descProd_zero_rnd]
  | succ n ih =>
    rw [descProd_succ_top_rnd, descProd_succ_top_rnd, H n (by omega),
      ih fun i hi ↦ H i (by omega)]

/-! ### The rounds as a periodic sequence on `ℕ` -/

/-- The rounds `R_(i mod s)` as an `s`-periodic sequence on `ℕ`. -/
private def orbRoundSeq (r s : ℕ) (L : ℕ → G) (i : ℕ) : G := L (pairIdxR r s (i % s))

/-- The group identity behind the wrapped windows. -/
private theorem wrap_window_identity_rnd (a b c d e x z : G) (h1 : c * a * e = 1)
    (h2 : d * b * x * z = 1) (h3 : d * e = 1) : a * b = c⁻¹ * z⁻¹ * x⁻¹ := by
  have hd : d = e⁻¹ := eq_inv_of_mul_eq_one_left h3
  subst hd
  calc a * b = c⁻¹ * (c * a * e) * (e⁻¹ * b * x * z) * z⁻¹ * x⁻¹ := by group
    _ = _ := by rw [h1, h2]; group

/-- All windows of length `r` of the rounds have the product `C⁻¹ A⁻¹ B⁻¹` (the proof of
`pairRoundSeq_window` in `AJHandoff.TorusKnot.PairKPeriComp`). -/
private theorem orbRoundSeq_window {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (p : ℕ) :
    descProd (orbRoundSeq r s L) p r =
      (L (pairIdxC r s))⁻¹ * (descProd L 0 (r - 2))⁻¹ * (L (pairIdxB r s))⁻¹ := by
  obtain ⟨hr, hrs, -⟩ := h
  have hs : 0 < s := by omega
  have hmod : descProd (orbRoundSeq r s L) p r = descProd (orbRoundSeq r s L) (p % s) r :=
    descProd_congr_rnd _ _ _ _ _ fun i _ ↦ by simp only [orbRoundSeq, Nat.mod_add_mod]
  rw [hmod]
  have hp' : p % s < s := Nat.mod_lt _ hs
  generalize p % s = q at hp' ⊢
  have hlow : ∀ a n, a + n ≤ s →
      descProd (orbRoundSeq r s L) a n = descProd (fun u ↦ L (pairIdxR r s u)) a n :=
    fun a n han ↦ descProd_congr_rnd _ _ _ _ _ fun i hi ↦ by
      simp only [orbRoundSeq, Nat.mod_eq_of_lt (show a + i < s by omega)]
  by_cases hc : q + r ≤ s
  · have h1 := hL.stairHigh (q + r - 1) (by omega) (by omega)
    rw [show q + r - 1 + 1 - r = q by omega] at h1
    rw [hlow q r hc]
    calc _ = (L (pairIdxC r s))⁻¹ * (L (pairIdxC r s) *
          descProd (fun u ↦ L (pairIdxR r s u)) q r * L (pairIdxB r s) * descProd L 0 (r - 2)) *
          (descProd L 0 (r - 2))⁻¹ * (L (pairIdxB r s))⁻¹ := by group
      _ = _ := by rw [h1]; group
  · obtain ⟨t, ht⟩ : ∃ t, q + r = s + t + 1 := ⟨q + r - s - 1, by omega⟩
    rw [show descProd (orbRoundSeq r s L) q r =
        descProd (orbRoundSeq r s L) q ((t + 1) + (s - q)) by congr 1; omega,
      descProd_add_rnd, show q + (s - q) = s by omega,
      hlow q (s - q) (by omega)]
    have hwrap : descProd (orbRoundSeq r s L) s (t + 1) =
        descProd (fun u ↦ L (pairIdxR r s u)) 0 (t + 1) :=
      descProd_congr_rnd _ _ _ _ _ fun i hi ↦ by
        simp only [orbRoundSeq, Nat.zero_add, Nat.add_mod_left,
          Nat.mod_eq_of_lt (show i < s by omega)]
    rw [hwrap]
    have h1 := hL.stairLow t (by omega)
    have h2 := hL.climb (s + t) (by omega) (by omega)
    rw [show s + r - 2 - (s + t) = r - 2 - t by omega, show s + t - s = t by omega,
      show s + t + 1 - r = q by omega, show s + r - 1 - (s + t) = s - q by omega] at h2
    have h3 : descProd (fun j ↦ L (pairIdxDp r s j)) (r - 2 - t) t * descProd L 0 t = 1 := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        simp [descProd_zero_rnd]
      · exact hL.bot t h0 (by omega)
    exact wrap_window_identity_rnd _ _ _ _ _ _ _ h1 h2 h3

/-- The index of `y_(p + i)` on `ℕ`. -/
private theorem toNat_emod_add_rnd {s : ℕ} (hs : 0 < s) (p : ℤ) (i : ℕ) :
    ((p + i) % (s : ℤ)).toNat = ((p % s).toNat + i) % s := by
  have hs' : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
  have h1 : (((p + i) % (s : ℤ)).toNat : ℤ) = ((((p % s).toNat + i) % s : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hs'), Int.natCast_mod, Nat.cast_add,
      Int.toNat_of_nonneg (Int.emod_nonneg _ hs'), Int.emod_add_emod]
  exact_mod_cast h1

omit [Group G] in
/-- The rounds `y_(p + k)` as the `ℕ`-sequence shifted to `(p mod s)`. -/
private theorem pairOrbY_eq_orbRoundSeq {s : ℕ} (hs : 0 < s) (r : ℕ) (L : ℕ → G) (p : ℤ)
    (i : ℕ) : pairOrbY r s L (p + i) = orbRoundSeq r s L ((p % s).toNat + i) := by
  rw [pairOrbY, orbRoundSeq, toNat_emod_add_rnd hs]

set_option linter.unusedSectionVars false in
theorem pairOrbY_add_period (r s : ℕ) (L : ℕ → G) (i : ℤ) :
    pairOrbY r s L (i + s) = pairOrbY r s L i := by
  simp only [pairOrbY, Int.add_emod_right]

set_option linter.unusedSectionVars false in
theorem pairOrbY_add_mul_period (r s : ℕ) (L : ℕ → G) (i k : ℤ) :
    pairOrbY r s L (i + s * k) = pairOrbY r s L i := by
  simp only [pairOrbY, Int.add_mul_emod_self_left]

set_option linter.unusedSectionVars false in
theorem pairOrbY_natCast {r s : ℕ} (L : ℕ → G) {i : ℕ} (hi : i < s) :
    pairOrbY r s L i = L (pairIdxR r s i) := by
  have hs : (0 : ℤ) ≤ i := Int.natCast_nonneg i
  rw [pairOrbY, Int.emod_eq_of_lt hs (by exact_mod_cast hi), Int.toNat_natCast]

/-- Every `r` consecutive rounds have the product `K`. -/
theorem pairOrb_window {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G} (hL : PairGapRels r s L)
    (p : ℤ) : descProd (fun k ↦ pairOrbY r s L (p + k)) 0 r = pairOrbK r s L := by
  have hs : 0 < s := by have := h.2.1; omega
  rw [descProd_congr_rnd (fun k : ℕ ↦ pairOrbY r s L (p + k)) (orbRoundSeq r s L) 0
    (p % s).toNat r fun i _ ↦ by rw [Nat.zero_add, pairOrbY_eq_orbRoundSeq hs],
    orbRoundSeq_window h L hL]
  rfl

/-- Conjugation by `K` shifts the rounds by `r` (one step). -/
private theorem pairOrbK_conj_rnd {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G}
    (hL : PairGapRels r s L) (i : ℤ) :
    pairOrbK r s L * pairOrbY r s L i * (pairOrbK r s L)⁻¹ = pairOrbY r s L (i + r) := by
  have hr : 1 ≤ r := by have := h.1; omega
  have w0 := pairOrb_window h hL i
  have w1 := pairOrb_window h hL (i + 1)
  rw [descProd_split_bot_rnd _ hr] at w0
  rw [descProd_split_top_rnd _ hr] at w1
  have hM : descProd (fun k : ℕ ↦ pairOrbY r s L (i + k)) 1 (r - 1) =
      descProd (fun k : ℕ ↦ pairOrbY r s L (i + 1 + k)) 0 (r - 1) :=
    descProd_congr_rnd _ _ _ _ _ fun j _ ↦ by congr 1; push_cast; ring
  rw [hM] at w0
  have e1 : pairOrbY r s L (i + ((0 : ℕ) : ℤ)) = pairOrbY r s L i := by
    congr 1; push_cast; ring
  have e2 : pairOrbY r s L (i + 1 + ((r - 1 : ℕ) : ℤ)) = pairOrbY r s L (i + r) := by
    congr 1; push_cast [Nat.cast_sub hr]; ring
  rw [e1] at w0
  rw [e2] at w1
  calc pairOrbK r s L * pairOrbY r s L i * (pairOrbK r s L)⁻¹ =
      pairOrbK r s L * pairOrbY r s L i *
        (descProd (fun k : ℕ ↦ pairOrbY r s L (i + 1 + k)) 0 (r - 1) * pairOrbY r s L i)⁻¹ := by
        rw [w0]
    _ = pairOrbK r s L *
        (descProd (fun k : ℕ ↦ pairOrbY r s L (i + 1 + k)) 0 (r - 1))⁻¹ := by group
    _ = _ := by rw [← w1]; group

/-- Conjugation by `K` shifts the rounds by `r`. -/
theorem pairOrbK_zpow_conj {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G} (hL : PairGapRels r s L)
    (i w : ℤ) :
    pairOrbK r s L ^ w * pairOrbY r s L i * pairOrbK r s L ^ (-w) =
      pairOrbY r s L (i + r * w) := by
  have hn : ∀ (n : ℕ) (i : ℤ), pairOrbK r s L ^ (n : ℤ) * pairOrbY r s L i *
      pairOrbK r s L ^ (-(n : ℤ)) = pairOrbY r s L (i + r * n) := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      intro i
      calc pairOrbK r s L ^ ((n + 1 : ℕ) : ℤ) * pairOrbY r s L i *
          pairOrbK r s L ^ (-((n + 1 : ℕ) : ℤ)) = pairOrbK r s L ^ (n : ℤ) *
            (pairOrbK r s L * pairOrbY r s L i * (pairOrbK r s L)⁻¹) *
            pairOrbK r s L ^ (-(n : ℤ)) := by push_cast; group
        _ = _ := by
          rw [pairOrbK_conj_rnd h hL, ih]
          congr 1
          push_cast
          ring
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg w
  · exact hn n i
  · have e := hn n (i + r * -n)
    rw [show i + r * -(n : ℤ) + r * n = i by ring] at e
    rw [← e, neg_neg]
    group

/-- The top-right climb, the left climbs and the right descents in terms of the rounds. -/
theorem pairOrb_climbs {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G} (hL : PairGapRels r s L) :
    L (pairIdxC r s) = (pairOrbY r s L 0)⁻¹ ∧
      (∀ n, n ≤ r - 2 → descProd L 0 n = (pairOrbY r s L 0)⁻¹ *
        (descProd (fun k ↦ pairOrbY r s L k) 1 n)⁻¹ * pairOrbY r s L 0) ∧
      (∀ n, n ≤ r - 2 → descProd (fun j ↦ L (pairIdxDp r s j)) (r - 2 - n) n =
        (pairOrbY r s L 0)⁻¹ * descProd (fun k ↦ pairOrbY r s L k) 1 n * pairOrbY r s L 0) := by
  obtain ⟨hr, hrs, -⟩ := h
  have hs : 0 < s := by omega
  have hy : ∀ k : ℕ, k < s → pairOrbY r s L k = L (pairIdxR r s k) :=
    fun k hk ↦ pairOrbY_natCast L hk
  have hC : L (pairIdxC r s) = (pairOrbY r s L 0)⁻¹ := by
    have h0 := hL.stairLow 0 (by omega)
    rw [descProd_one_rnd, descProd_zero_rnd, mul_one] at h0
    rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) by rfl, hy 0 hs, eq_inv_iff_mul_eq_one]
    simpa using h0
  have hA : ∀ n, n ≤ r - 2 → descProd L 0 n = (pairOrbY r s L 0)⁻¹ *
      (descProd (fun k ↦ pairOrbY r s L k) 1 n)⁻¹ * pairOrbY r s L 0 := by
    intro n hn
    have h0 := hL.stairLow n hn
    rw [descProd_succ_bot_rnd, hC] at h0
    have hR : descProd (fun u ↦ L (pairIdxR r s u)) (0 + 1) n =
        descProd (fun k ↦ pairOrbY r s L k) 1 n :=
      descProd_congr_rnd _ _ _ _ _ fun i hi ↦ by rw [hy _ (by omega)]
    rw [hR, show L (pairIdxR r s 0) = pairOrbY r s L 0 by
      rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) by rfl, hy 0 hs]] at h0
    calc descProd L 0 n = (pairOrbY r s L 0)⁻¹ *
          (descProd (fun k ↦ pairOrbY r s L k) 1 n)⁻¹ * pairOrbY r s L 0 *
          ((pairOrbY r s L 0)⁻¹ * (descProd (fun k ↦ pairOrbY r s L k) 1 n *
            pairOrbY r s L 0) * descProd L 0 n) := by group
      _ = _ := by rw [h0, mul_one]
  refine ⟨hC, hA, fun n hn ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp [descProd_zero_rnd]
  · have hb := hL.bot n h0 hn
    rw [hA n hn] at hb
    calc descProd (fun j ↦ L (pairIdxDp r s j)) (r - 2 - n) n =
        descProd (fun j ↦ L (pairIdxDp r s j)) (r - 2 - n) n * ((pairOrbY r s L 0)⁻¹ *
          (descProd (fun k ↦ pairOrbY r s L k) 1 n)⁻¹ * pairOrbY r s L 0) *
          ((pairOrbY r s L 0)⁻¹ * descProd (fun k ↦ pairOrbY r s L k) 1 n *
            pairOrbY r s L 0) := by group
      _ = _ := by rw [hb, one_mul]

/-- The big climb and the run blocks are `y_(-1)⁻¹`. -/
theorem pairOrb_runs {r s : ℕ} (h : IsTorusPair r s) {L : ℕ → G} (hL : PairGapRels r s L) :
    L (pairIdxB r s) = (pairOrbY r s L (-1))⁻¹ ∧
      ∀ n, r - 1 ≤ n → n ≤ 2 * pairC r s - s - r →
        L (pairIdxRun r s n) = (pairOrbY r s L (-1))⁻¹ := by
  obtain ⟨hC, hA, -⟩ := pairOrb_climbs h hL
  have hr : 2 ≤ r := h.1
  have hrs : r < s := h.2.1
  have hs : 0 < s := by omega
  have hB : L (pairIdxB r s) = (pairOrbY r s L (-1))⁻¹ := by
    have w := pairOrb_window h hL (-1)
    rw [show descProd (fun k : ℕ ↦ pairOrbY r s L (-1 + k)) 0 r =
        descProd (fun k : ℕ ↦ pairOrbY r s L (-1 + k)) 0 ((r - 2) + 2) by
          rw [Nat.sub_add_cancel hr], descProd_add_rnd, descProd_succ_top_rnd,
      descProd_one_rnd] at w
    have hY : descProd (fun k : ℕ ↦ pairOrbY r s L (-1 + k)) (0 + 2) (r - 2) =
        descProd (fun k : ℕ ↦ pairOrbY r s L k) 1 (r - 2) :=
      descProd_congr_rnd _ _ _ _ _ fun j _ ↦ by congr 1; push_cast; ring
    have e0 : pairOrbY r s L (-1 + ((0 + 1 : ℕ) : ℤ)) = pairOrbY r s L 0 := by
      congr 1
    have e1 : pairOrbY r s L (-1 + ((0 : ℕ) : ℤ)) = pairOrbY r s L (-1) := by
      congr 1
    rw [hY, e0, e1] at w
    have hK : pairOrbK r s L = descProd (fun k : ℕ ↦ pairOrbY r s L k) 1 (r - 2) *
        (pairOrbY r s L 0 * (L (pairIdxB r s))⁻¹) := by
      unfold pairOrbK
      rw [hC, hA (r - 2) le_rfl]
      group
    rw [hK] at w
    rw [mul_left_cancel (mul_left_cancel w), inv_inv]
  refine ⟨hB, fun n hn1 hn2 ↦ ?_⟩
  have h1 := hL.run n hn1 hn2
  have h2 := hL.climb (s + r - 2) (by omega) (by omega)
  rw [show s + r - 2 - (s + r - 2) = 0 by omega, show s + r - 2 - s = r - 2 by omega,
    show s + r - 2 + 1 - r = s - 1 by omega, show s + r - 1 - (s + r - 2) = 1 by omega,
    descProd_one_rnd] at h2
  rw [← hB]
  exact mul_left_cancel (mul_right_cancel (h1.trans h2.symm))

end AJConjecture
