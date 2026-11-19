import Mathlib
import AJHandoff.TorusKnot.PairKPeriGapRel
import AJHandoff.TorusKnot.PairKTorusGroup

/-!
# The companion tuple of `pairBlocks r s`

From the block loops `L q` of `pairBlocks r s`: the window `w_0, …, w_(r-1)` of the staircase,
`w_0 = R_0`, `w_1 = B⁻¹` and, for `2 ≤ n ≤ r - 1`, `w_n = B Q A_(r-1-n)⁻¹ Q⁻¹ B⁻¹` with
`Q = A_(r-3) ⋯ A_(r-n)`. With `X_(-n) = w_n` and `X_t = R_t` (`t ≤ s - 1`) all products of `r`
consecutive terms `X_t X_(t-1) ⋯ X_(t-r+1)` agree (the staircase relations), and the climb
relations make the sequence `s`-periodic: the window is fixed by `(σ_(r-2) ⋯ σ_0)^s`. The
companion tuple `z_k = (w_1 ⋯ w_(r-2-k)) w_(r-1-k) (w_1 ⋯ w_(r-2-k))⁻¹` is the half twist on
the first `r - 1` entries of the rotated window `(w_1, …, w_(r-1), w_0)`; it is fixed by
`(σ_0 ⋯ σ_(r-2))^s` (`pairCompTuple_fixed`), so it gives the map from the group of `T(r, s)`.
Checked numerically (random `SU(3)` representations of `T(r, s)`) for
`(r, s) ∈ {(2,5), (3,4), (3,5), (3,7), (3,8), (4,5), (4,7), (5,7), (4,9), (5,8), (3,11), (6,7)}`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The staircase window `w_n = X_(-n)`, `n ≤ r - 1`, in terms of the block loops. -/
def pairWin (r s : ℕ) (L : ℕ → G) (n : ℕ) : G :=
  if n = 0 then L (pairIdxR r s 0)
  else if n = 1 then (L (pairIdxB r s))⁻¹
  else L (pairIdxB r s) * descProd L (r - n) (n - 2) * (L (r - 1 - n))⁻¹ *
    (descProd L (r - n) (n - 2))⁻¹ * (L (pairIdxB r s))⁻¹

/-- The entries `z_k = (w_1 ⋯ w_(r-2-k)) w_(r-1-k) (w_1 ⋯ w_(r-2-k))⁻¹` of the companion
tuple. -/
def pairCompFun (r s : ℕ) (L : ℕ → G) (k : ℕ) : G :=
  ((List.range (r - 2 - k)).map fun i ↦ pairWin r s L (i + 1)).prod * pairWin r s L (r - 1 - k) *
    (((List.range (r - 2 - k)).map fun i ↦ pairWin r s L (i + 1)).prod)⁻¹

/-- The companion tuple on `r` strands. -/
def pairCompTuple (r s : ℕ) (L : ℕ → G) : Fin r → G := fun k ↦ pairCompFun r s L k

/-- The image `Π^s z_0^(-rs)` of the companion longitude. -/
def pairCompLong (r s : ℕ) (L : ℕ → G) : G :=
  ((List.finRange r).map (pairCompTuple r s L)).prod ^ s *
    pairCompFun r s L 0 ^ (-((r * s : ℕ) : ℤ))

/-! ### Descending products -/

/-- The empty descending product. -/
private theorem descProd_zero_comp (g : ℕ → G) (a : ℕ) : descProd g a 0 = 1 := by
  simp [descProd]

/-- Splitting off the top factor of a descending product. -/
private theorem descProd_succ_top_comp (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = g (a + n) * descProd g a n := by
  simp [descProd, List.range_succ]

/-- Splitting off the bottom factor of a descending product. -/
private theorem descProd_succ_bot_comp (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = descProd g (a + 1) n * g a := by
  induction n with
  | zero => simp [descProd]
  | succ n ih =>
    rw [descProd_succ_top_comp, ih, descProd_succ_top_comp, mul_assoc,
      show a + 1 + n = a + (n + 1) by omega]

/-- Splitting a descending product into an upper and a lower part. -/
private theorem descProd_add_comp (g : ℕ → G) (a n k : ℕ) :
    descProd g a (n + k) = descProd g (a + k) n * descProd g a k := by
  induction n with
  | zero => simp [descProd_zero_comp]
  | succ n ih =>
    rw [show n + 1 + k = n + k + 1 by omega, descProd_succ_top_comp, ih, descProd_succ_top_comp,
      mul_assoc, show a + (n + k) = a + k + n by omega]

/-- Descending products with the same factors agree. -/
private theorem descProd_congr_comp (g h : ℕ → G) (a b n : ℕ)
    (H : ∀ i, i < n → g (a + i) = h (b + i)) : descProd g a n = descProd h b n := by
  induction n with
  | zero => simp [descProd_zero_comp]
  | succ n ih =>
    rw [descProd_succ_top_comp, descProd_succ_top_comp, H n (by omega),
      ih fun i hi ↦ H i (by omega)]

/-- A descending product read in increasing order of the list index. -/
private theorem descProd_eq_prod_range_comp (g : ℕ → G) (a n : ℕ) :
    descProd g a n = ((List.range n).map fun i ↦ g (a + n - 1 - i)).prod := by
  induction n with
  | zero => simp [descProd_zero_comp]
  | succ n ih =>
    rw [descProd_succ_top_comp, ih, List.range_succ_eq_map, List.map_cons, List.prod_cons,
      List.map_map]
    congr 2
    · refine List.map_congr_left fun i hi ↦ ?_
      simp only [Function.comp_apply]
      congr 1
      have := List.mem_range.1 hi
      omega

/-! ### The companion tuple of a sequence -/

/-- The companion tuple read from the window `y (p + r - 1), …, y p` of a sequence. -/
private def seqComp (r : ℕ) (y : ℕ → G) (p k : ℕ) : G :=
  descProd y (p + k + 1) (r - 2 - k) * y (p + k) * (descProd y (p + k + 1) (r - 2 - k))⁻¹

/-- The window relation `y (p + r) = (y (p + r - 1) ⋯ y (p + 1)) y p (⋯)⁻¹`. -/
private def SeqWindowRel (r : ℕ) (y : ℕ → G) : Prop :=
  ∀ p, y (p + r) = descProd y (p + 1) (r - 1) * y p * (descProd y (p + 1) (r - 1))⁻¹

/-- The first entry of the companion tuple, by the window relation. -/
private theorem seqComp_zero_eq {r : ℕ} (hr : 2 ≤ r) {y : ℕ → G} (hy : SeqWindowRel r y)
    (q : ℕ) : seqComp r y q 0 = (y (q + r - 1))⁻¹ * y (q + r) * y (q + r - 1) := by
  rw [hy q, show r - 1 = r - 2 + 1 by omega, descProd_succ_top_comp,
    show q + 1 + (r - 2) = q + r - 1 by omega, seqComp]
  simp only [Nat.add_zero, Nat.sub_zero]
  group

/-- The last entry of the companion tuple is the newest term. -/
private theorem seqComp_succ_last {r : ℕ} (hr : 2 ≤ r) (y : ℕ → G) (q : ℕ) :
    seqComp r y (q + 1) (r - 1) = y (q + r) := by
  rw [seqComp, show r - 2 - (r - 1) = 0 by omega, descProd_zero_comp,
    show q + 1 + (r - 1) = q + r by omega]
  group

/-- Shifting the window by one conjugates the entries by the newest old term. -/
private theorem seqComp_succ_of_le {r : ℕ} (hr : 2 ≤ r) (y : ℕ → G) (q k : ℕ)
    (hk : k ≤ r - 2) :
    seqComp r y (q + 1) k = y (q + r - 1) * seqComp r y q (k + 1) * (y (q + r - 1))⁻¹ := by
  rcases Nat.lt_or_ge k (r - 2) with h | h
  · rw [seqComp, seqComp, show r - 2 - k = r - 2 - (k + 1) + 1 by omega, descProd_succ_top_comp,
      show q + 1 + k + 1 = q + (k + 1) + 1 by omega,
      show q + (k + 1) + 1 + (r - 2 - (k + 1)) = q + r - 1 by omega,
      show q + 1 + k = q + (k + 1) by omega]
    group
  · rw [seqComp, seqComp, show r - 2 - k = 0 by omega, show r - 2 - (k + 1) = 0 by omega,
      show q + 1 + k = q + r - 1 by omega, show q + (k + 1) = q + r - 1 by omega]
    simp only [descProd_zero_comp]
    group

/-- One copy of `δ` on the companion tuple of the window at `q`. -/
private theorem seqComp_delta {r : ℕ} (hr : 2 ≤ r) {y : ℕ → G} (hy : SeqWindowRel r y)
    (q : ℕ) (k : Fin r) :
    seqComp r y q 0 * seqComp r y q (((k : ℕ) + 1) % r) * (seqComp r y q 0)⁻¹ =
      (y (q + r - 1))⁻¹ * y (q + r) * seqComp r y (q + 1) k *
        ((y (q + r - 1))⁻¹ * y (q + r))⁻¹ := by
  have hk := k.isLt
  rcases Nat.lt_or_ge ((k : ℕ) + 1) r with h | h
  · rw [Nat.mod_eq_of_lt h, seqComp_succ_of_le hr y q k (by omega), seqComp_zero_eq hr hy]
    group
  · rw [show (k : ℕ) + 1 = r by omega, Nat.mod_self, show (k : ℕ) = r - 1 by omega,
      seqComp_succ_last hr, seqComp_zero_eq hr hy]
    group

/-- `δ^(n+1) = δ^n δ` as braid words. -/
private theorem torusPairWord_succ_eq (r n : ℕ) :
    torusPairWord r (n + 1) = torusPairWord r n ++ torusPairWord r 1 := by
  rw [torusPairWord, torusPairWord, torusPairWord, List.replicate_succ', List.flatten_append]
  simp

/-- The run of `δ^n` on the companion tuple of a sequence with the window relation. -/
private theorem braidRun_seqComp {r : ℕ} (hr : 2 ≤ r) {y : ℕ → G} (hy : SeqWindowRel r y)
    (p n : ℕ) (k : Fin r) :
    (braidRun r (torusPairWord r n) fun j : Fin r ↦ seqComp r y p j).1 k =
      (y (p + r - 1))⁻¹ * y (p + n + r - 1) * seqComp r y (p + n) k *
        ((y (p + r - 1))⁻¹ * y (p + n + r - 1))⁻¹ := by
  have hr0 : 0 < r := by omega
  induction n generalizing k with
  | zero =>
    simp only [torusPairWord, List.replicate_zero, List.flatten_nil, braidRun, List.foldl_nil,
      Nat.add_zero]
    group
  | succ n ih =>
    rw [torusPairWord_succ_eq, braidRun_append, braidRun_torusPairWord_fst hr0 1]
    simp only [List.range_one, List.map_singleton, List.prod_singleton, Nat.zero_mod]
    rw [ih, ih]
    have hd := seqComp_delta hr hy (p + n) k
    rw [show p + (n + 1) = p + n + 1 by omega, show p + n + 1 + r - 1 = p + n + r by omega]
    calc _ = (y (p + r - 1))⁻¹ * y (p + n + r - 1) * (seqComp r y (p + n) 0 *
          seqComp r y (p + n) (((k : ℕ) + 1) % r) * (seqComp r y (p + n) 0)⁻¹) *
          ((y (p + r - 1))⁻¹ * y (p + n + r - 1))⁻¹ := by group
      _ = _ := by rw [hd]; group

/-- The companion tuple of an `s`-periodic sequence is `s`-periodic in the offset. -/
private theorem seqComp_add_period (r s : ℕ) {y : ℕ → G} (hp : ∀ i, y (i + s) = y i)
    (p k : ℕ) : seqComp r y (p + s) k = seqComp r y p k := by
  have h : ∀ a n, descProd y (a + s) n = descProd y a n := fun a n ↦
    descProd_congr_comp y y _ _ n fun i _ ↦ by rw [show a + s + i = a + i + s by omega, hp]
  rw [seqComp, seqComp, show p + s + k + 1 = p + k + 1 + s by omega, h,
    show p + s + k = p + k + s by omega, hp]

/-- `δ^s` fixes the companion tuple of an `s`-periodic sequence with the window relation. -/
private theorem braidRun_seqComp_of_period {r s : ℕ} (hr : 2 ≤ r) {y : ℕ → G}
    (hy : SeqWindowRel r y) (hp : ∀ i, y (i + s) = y i) (p : ℕ) :
    (braidRun r (torusPairWord r s) fun j : Fin r ↦ seqComp r y p j).1 =
      fun j : Fin r ↦ seqComp r y p j := by
  funext k
  rw [braidRun_seqComp hr hy, seqComp_add_period r s hp,
    show p + s + r - 1 = p + r - 1 + s by omega, hp]
  group

/-- A sequence all of whose windows of length `r` have the same product has the window
relation. -/
private theorem seqWindowRel_of_const {r : ℕ} (hr : 1 ≤ r) {y : ℕ → G} (K : G)
    (hK : ∀ p, descProd y p r = K) : SeqWindowRel r y := by
  intro p
  have h1 := hK (p + 1)
  have h2 := hK p
  rw [show r = r - 1 + 1 by omega, descProd_succ_top_comp,
    show p + 1 + (r - 1) = p + r by omega] at h1
  rw [show r = r - 1 + 1 by omega, descProd_succ_bot_comp] at h2
  rw [eq_mul_inv_of_mul_eq h1, ← h2]

/-! ### The rounds of `pairBlocks r s` as a periodic sequence -/

/-- The rounds `R_(i mod s)` as an `s`-periodic sequence. -/
private def pairRoundSeq (r s : ℕ) (L : ℕ → G) (i : ℕ) : G := L (pairIdxR r s (i % s))

omit [Group G] in
/-- The rounds sequence has period `s`. -/
private theorem pairRoundSeq_add_period (r s : ℕ) (L : ℕ → G) (i : ℕ) :
    pairRoundSeq r s L (i + s) = pairRoundSeq r s L i := by
  simp only [pairRoundSeq, Nat.add_mod_right]

/-- The group identity behind the wrapped windows. -/
private theorem wrap_window_identity (a b c d e x z : G) (h1 : c * a * e = 1)
    (h2 : d * b * x * z = 1) (h3 : d * e = 1) : a * b = c⁻¹ * z⁻¹ * x⁻¹ := by
  have hd : d = e⁻¹ := eq_inv_of_mul_eq_one_left h3
  subst hd
  calc a * b = c⁻¹ * (c * a * e) * (e⁻¹ * b * x * z) * z⁻¹ * x⁻¹ := by group
    _ = _ := by rw [h1, h2]; group

/-- All windows of length `r` of the rounds have the product `C⁻¹ A⁻¹ B⁻¹`. -/
private theorem pairRoundSeq_window {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (p : ℕ) :
    descProd (pairRoundSeq r s L) p r =
      (L (pairIdxC r s))⁻¹ * (descProd L 0 (r - 2))⁻¹ * (L (pairIdxB r s))⁻¹ := by
  obtain ⟨hr, hrs, -⟩ := h
  have hs : 0 < s := by omega
  have hmod : descProd (pairRoundSeq r s L) p r = descProd (pairRoundSeq r s L) (p % s) r :=
    descProd_congr_comp _ _ _ _ _ fun i _ ↦ by simp only [pairRoundSeq, Nat.mod_add_mod]
  rw [hmod]
  have hp' : p % s < s := Nat.mod_lt _ hs
  generalize p % s = q at hp' ⊢
  have hlow : ∀ a n, a + n ≤ s →
      descProd (pairRoundSeq r s L) a n = descProd (fun u ↦ L (pairIdxR r s u)) a n :=
    fun a n han ↦ descProd_congr_comp _ _ _ _ _ fun i hi ↦ by
      simp only [pairRoundSeq, Nat.mod_eq_of_lt (show a + i < s by omega)]
  by_cases hc : q + r ≤ s
  · have h1 := hL.stairHigh (q + r - 1) (by omega) (by omega)
    rw [show q + r - 1 + 1 - r = q by omega] at h1
    rw [hlow q r hc]
    calc _ = (L (pairIdxC r s))⁻¹ * (L (pairIdxC r s) *
          descProd (fun u ↦ L (pairIdxR r s u)) q r * L (pairIdxB r s) * descProd L 0 (r - 2)) *
          (descProd L 0 (r - 2))⁻¹ * (L (pairIdxB r s))⁻¹ := by group
      _ = _ := by rw [h1]; group
  · obtain ⟨t, ht⟩ : ∃ t, q + r = s + t + 1 := ⟨q + r - s - 1, by omega⟩
    rw [show descProd (pairRoundSeq r s L) q r =
        descProd (pairRoundSeq r s L) q ((t + 1) + (s - q)) by congr 1; omega,
      descProd_add_comp, show q + (s - q) = s by omega,
      hlow q (s - q) (by omega)]
    have hwrap : descProd (pairRoundSeq r s L) s (t + 1) =
        descProd (fun u ↦ L (pairIdxR r s u)) 0 (t + 1) :=
      descProd_congr_comp _ _ _ _ _ fun i hi ↦ by
        simp only [pairRoundSeq, Nat.zero_add, Nat.add_mod_left,
          Nat.mod_eq_of_lt (show i < s by omega)]
    rw [hwrap]
    have h1 := hL.stairLow t (by omega)
    have h2 := hL.climb (s + t) (by omega) (by omega)
    rw [show s + r - 2 - (s + t) = r - 2 - t by omega, show s + t - s = t by omega,
      show s + t + 1 - r = q by omega, show s + r - 1 - (s + t) = s - q by omega] at h2
    have h3 : descProd (fun j ↦ L (pairIdxDp r s j)) (r - 2 - t) t * descProd L 0 t = 1 := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        simp [descProd_zero_comp]
      · exact hL.bot t h0 (by omega)
    exact wrap_window_identity _ _ _ _ _ _ _ h1 h2 h3

/-- The window relation of the rounds. -/
private theorem pairRoundSeq_windowRel {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) : SeqWindowRel r (pairRoundSeq r s L) :=
  seqWindowRel_of_const (by have := h.1; omega) _ (pairRoundSeq_window h L hL)

/-! ### The staircase window in terms of the rounds -/

/-- The products `w_1 ⋯ w_n` of the window. -/
private theorem pairWin_prefix {r s : ℕ} (L : ℕ → G) (n : ℕ) (hn : 1 ≤ n) (hnr : n ≤ r - 1) :
    ((List.range n).map fun i ↦ pairWin r s L (i + 1)).prod =
      (descProd L (r - 1 - n) (n - 1))⁻¹ * (L (pairIdxB r s))⁻¹ := by
  induction n, hn using Nat.le_induction with
  | base => simp [pairWin, descProd_zero_comp]
  | succ n hn ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih (by omega), List.map_singleton,
      List.prod_singleton]
    simp only [pairWin, show n + 1 ≠ 0 by omega, show n + 1 ≠ 1 by omega, ↓reduceIte]
    rw [show r - (n + 1) = r - 1 - n by omega, show n + 1 - 2 = n - 1 by omega,
      show r - 1 - (n + 1) = r - 2 - n by omega, show n + 1 - 1 = n - 1 + 1 by omega,
      descProd_succ_bot_comp, show r - 2 - n + 1 = r - 1 - n by omega]
    group

/-- The products `R_(s-1) ⋯ R_(s-n)` of the last rounds. -/
private theorem pairRound_suffix {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (n : ℕ) (hn : 1 ≤ n) (hnr : n ≤ r - 1) :
    descProd (fun u ↦ L (pairIdxR r s u)) (s - n) n =
      (descProd L (r - 1 - n) (n - 1))⁻¹ * (L (pairIdxB r s))⁻¹ := by
  obtain ⟨hr, hrs, -⟩ := h
  have h2 := hL.climb (s + (r - 1 - n)) (by omega) (by omega)
  rw [show s + r - 2 - (s + (r - 1 - n)) = n - 1 by omega,
    show s + (r - 1 - n) - s = r - 1 - n by omega,
    show s + (r - 1 - n) + 1 - r = s - n by omega,
    show s + r - 1 - (s + (r - 1 - n)) = n by omega,
    show r - 2 = (n - 1) + (r - 1 - n) by omega, descProd_add_comp, Nat.zero_add] at h2
  have h3 : descProd (fun j ↦ L (pairIdxDp r s j)) (n - 1) (r - 1 - n) *
      descProd L 0 (r - 1 - n) = 1 := by
    rcases Nat.eq_zero_or_pos (r - 1 - n) with h0 | h0
    · rw [h0]
      simp [descProd_zero_comp]
    · have := hL.bot (r - 1 - n) h0 (by omega)
      rwa [show r - 2 - (r - 1 - n) = n - 1 by omega] at this
  have hd := eq_inv_of_mul_eq_one_left h3
  rw [hd] at h2
  calc _ = descProd L 0 (r - 1 - n) * ((descProd L 0 (r - 1 - n))⁻¹ *
        descProd (fun u ↦ L (pairIdxR r s u)) (s - n) n * L (pairIdxB r s) *
        (descProd L (r - 1 - n) (n - 1) * descProd L 0 (r - 1 - n))) *
        (descProd L 0 (r - 1 - n))⁻¹ * (descProd L (r - 1 - n) (n - 1))⁻¹ *
        (L (pairIdxB r s))⁻¹ := by group
    _ = _ := by rw [h2]; group

/-- The products `w_1 ⋯ w_n` are the products `R_(s-1) ⋯ R_(s-n)`. -/
private theorem pairWin_prefix_eq_round {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (n : ℕ) (hnr : n ≤ r - 1) :
    ((List.range n).map fun i ↦ pairWin r s L (i + 1)).prod =
      descProd (fun u ↦ L (pairIdxR r s u)) (s - n) n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp [descProd_zero_comp]
  · rw [pairWin_prefix L n h0 hnr, pairRound_suffix h L hL n h0 hnr]

/-- The window entries are the last rounds: `w_j = R_(s-j)`, `w_0 = R_0`. -/
private theorem pairWin_eq_roundSeq {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (j : ℕ) (hj : j ≤ r - 1) :
    pairWin r s L j = pairRoundSeq r s L (s - j) := by
  have hrs := h.2.1
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    simp [pairWin, pairRoundSeq]
  · have hA := pairWin_prefix_eq_round h L hL j hj
    have hB := pairWin_prefix_eq_round h L hL (j - 1) (by omega)
    rw [show j = j - 1 + 1 by omega, List.range_succ, List.map_append, List.prod_append, hB,
      List.map_singleton, List.prod_singleton, descProd_succ_bot_comp,
      show s - (j - 1 + 1) + 1 = s - (j - 1) by omega] at hA
    rw [show j = j - 1 + 1 by omega, mul_left_cancel hA, pairRoundSeq,
      Nat.mod_eq_of_lt (show s - (j - 1 + 1) < s by omega)]

/-- The companion tuple is the companion tuple of the window of the rounds at `s - r + 1`. -/
private theorem pairCompFun_eq_seqComp {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) (k : ℕ) (hk : k < r) :
    pairCompFun r s L k = seqComp r (pairRoundSeq r s L) (s - r + 1) k := by
  have hrs := h.2.1
  have hW : ((List.range (r - 2 - k)).map fun i ↦ pairWin r s L (i + 1)).prod =
      descProd (pairRoundSeq r s L) (s - r + 1 + k + 1) (r - 2 - k) := by
    rw [descProd_eq_prod_range_comp]
    refine congrArg List.prod (List.map_congr_left fun i hi ↦ ?_)
    have hi' := List.mem_range.1 hi
    rw [pairWin_eq_roundSeq h L hL (i + 1) (by omega)]
    congr 1
    omega
  rw [pairCompFun, seqComp, hW, pairWin_eq_roundSeq h L hL (r - 1 - k) (by omega),
    show s - (r - 1 - k) = s - r + 1 + k by omega]

/-- The companion tuple of loops satisfying the gap relations is fixed by
`(σ_0 ⋯ σ_(r-2))^s`. -/
theorem pairCompTuple_fixed {r s : ℕ} (h : IsTorusPair r s) (L : ℕ → G)
    (hL : PairGapRels r s L) :
    (braidRun r (torusPairWord r s) (pairCompTuple r s L)).1 = pairCompTuple r s L := by
  have hfun : pairCompTuple r s L = fun j : Fin r ↦ seqComp r (pairRoundSeq r s L) (s - r + 1) j :=
    funext fun k ↦ pairCompFun_eq_seqComp h L hL k k.isLt
  rw [hfun]
  exact braidRun_seqComp_of_period h.1 (pairRoundSeq_windowRel h L hL)
    (pairRoundSeq_add_period r s L) _

end AJConjecture
