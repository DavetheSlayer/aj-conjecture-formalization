import Mathlib
import AJHandoff.TorusKnot.PairKPeriComp

/-!
# The block loops of the reverse construction

Given the images `y 0, …, y (r - 1)` of Artin's generators of `T(r, s)` under a representation
(a tuple fixed by `(σ_0 ⋯ σ_(r-2))^s`), `pairRevLoop r s y H` prescribes a loop for every block
of `pairBlocks r s`:

* the left climbs `A_k = y_k⁻¹`, the big climb `B = y_(r-2)⁻¹`, the right descents
  `D'_j = y_(r-3-j)`;
* the rounds `R_t = P(t+1) P(t)⁻¹`, where `P(n) = u_0 ⋯ u_(n-1)` is the cyclic product of the
  rotated tuple `u = (y_(r-1), y_0, …, y_(r-2))` (so `R_0 = y_(r-1)`), the top-right climb
  `C = R_0⁻¹` and every run block `R_(s-1)⁻¹`;
* the Hopf letters `H` and `H⁻¹`.

`pairGapRels_pairRevLoop`: these loops satisfy the gap relations. All relations but the climbs
hold by telescoping; the climbs say `P(s) P(s-k)⁻¹ = u_(r-k) ⋯ u_(r-1)`, which follows from the
torus relation `u_i = P(s) u_(i+s) P(s)⁻¹` (`pairRevPu_climb`).
`pairCompFun_pairRevLoop`: the companion tuple of these loops is `y` (the staircase window is
`w_0 = y_(r-1)`, `w_n = (y_(r-n) ⋯ y_(r-2))⁻¹ y_(r-1-n) (y_(r-n) ⋯ y_(r-2))`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The cyclic product `y_0 y_1 ⋯ y_(n-1)` of a tuple, indices modulo `r` (the conjugator of
`(σ_0 ⋯ σ_(r-2))^n`, see `braidRun_torusPairWord_fst`). -/
def pairRevCyc (r : ℕ) (y : ℕ → G) (n : ℕ) : G :=
  ((List.range n).map fun t ↦ y (t % r)).prod

/-- The cyclic product `u_0 u_1 ⋯ u_(n-1)` of the rotated tuple `u_i = y_((i + r - 1) mod r)`. -/
def pairRevPu (r : ℕ) (y : ℕ → G) (n : ℕ) : G :=
  ((List.range n).map fun i ↦ y ((i + r - 1) % r)).prod

/-- The rounds `R_t = P(t + 1) P(t)⁻¹ = P(t) u_t P(t)⁻¹`. -/
def pairRevRound (r : ℕ) (y : ℕ → G) (t : ℕ) : G :=
  pairRevPu r y (t + 1) * (pairRevPu r y t)⁻¹

/-- The prescribed loops of the blocks of `pairBlocks r s`, by position (`H` is the loop of the
first Hopf letter). -/
def pairRevLoop (r s : ℕ) (y : ℕ → G) (H : G) (q : ℕ) : G :=
  if q < r - 2 then (y q)⁻¹
  else if q < pairIdxB r s then (pairRevRound r y (s - 1))⁻¹
  else if q = pairIdxB r s then (y (r - 2))⁻¹
  else if q = pairIdxB r s + 1 then pairRevRound r y 0
  else if q = pairIdxB r s + 2 then H
  else if q ≤ pairIdxB r s + s + 1 then pairRevRound r y (q - pairIdxB r s - 2)
  else if q = pairIdxB r s + s + 2 then (pairRevRound r y 0)⁻¹
  else if q ≤ 2 * pairC r s then y (2 * pairC r s - q)
  else if q = 2 * pairC r s + 1 then H⁻¹
  else 1

/-! ### Descending products -/

private theorem descProd_zero_rl (g : ℕ → G) (a : ℕ) : descProd g a 0 = 1 := by
  simp [descProd]

private theorem descProd_succ_top_rl (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = g (a + n) * descProd g a n := by
  simp [descProd, List.range_succ]

private theorem descProd_succ_bot_rl (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = descProd g (a + 1) n * g a := by
  induction n with
  | zero => simp [descProd]
  | succ n ih =>
    rw [descProd_succ_top_rl, ih, descProd_succ_top_rl, mul_assoc,
      show a + 1 + n = a + (n + 1) by omega]

private theorem descProd_congr_rl (g h : ℕ → G) (a b n : ℕ)
    (H : ∀ i, i < n → g (a + i) = h (b + i)) : descProd g a n = descProd h b n := by
  induction n with
  | zero => simp [descProd_zero_rl]
  | succ n ih =>
    rw [descProd_succ_top_rl, descProd_succ_top_rl, H n (by omega),
      ih fun i hi ↦ H i (by omega)]

/-- The ascending product `y_a y_(a+1) ⋯ y_(b-1)`. -/
def pairRevAsc (y : ℕ → G) (a n : ℕ) : G := ((List.range n).map fun i ↦ y (a + i)).prod

theorem pairRevAsc_zero (y : ℕ → G) (a : ℕ) : pairRevAsc y a 0 = 1 := by simp [pairRevAsc]

theorem pairRevAsc_succ (y : ℕ → G) (a n : ℕ) :
    pairRevAsc y a (n + 1) = pairRevAsc y a n * y (a + n) := by
  simp [pairRevAsc, List.range_succ]

theorem pairRevAsc_succ_bot (y : ℕ → G) (a n : ℕ) :
    pairRevAsc y a (n + 1) = y a * pairRevAsc y (a + 1) n := by
  induction n with
  | zero => simp [pairRevAsc]
  | succ n ih =>
    rw [pairRevAsc_succ, ih, pairRevAsc_succ, mul_assoc, show a + 1 + n = a + (n + 1) by omega]

theorem pairRevAsc_add (y : ℕ → G) (a n k : ℕ) :
    pairRevAsc y a (n + k) = pairRevAsc y a n * pairRevAsc y (a + n) k := by
  induction k with
  | zero => simp [pairRevAsc_zero]
  | succ k ih =>
    rw [← Nat.add_assoc, pairRevAsc_succ, ih, pairRevAsc_succ, mul_assoc, Nat.add_assoc]

/-- A descending product of inverses is the inverse of the ascending product. -/
theorem descProd_inv_rl (y : ℕ → G) (a n : ℕ) :
    descProd (fun i ↦ (y i)⁻¹) a n = (pairRevAsc y a n)⁻¹ := by
  induction n with
  | zero => simp [descProd_zero_rl, pairRevAsc_zero]
  | succ n ih => rw [descProd_succ_top_rl, ih, pairRevAsc_succ, mul_inv_rev]

/-- A descending product read backwards along `j ↦ c - j` is an ascending product. -/
theorem descProd_rev_rl (y : ℕ → G) (c a n : ℕ) (h : a + n ≤ c + 1) :
    descProd (fun j ↦ y (c - j)) a n = pairRevAsc y (c + 1 - a - n) n := by
  induction n generalizing a with
  | zero => simp [descProd_zero_rl, pairRevAsc_zero]
  | succ n ih =>
    rw [descProd_succ_bot_rl, ih (a + 1) (by omega), pairRevAsc_succ,
      show c + 1 - (a + 1) - n = c + 1 - a - (n + 1) by omega,
      show c + 1 - a - (n + 1) + n = c - a by omega]

/-! ### The cyclic products -/

theorem pairRevPu_zero (r : ℕ) (y : ℕ → G) : pairRevPu r y 0 = 1 := by
  simp [pairRevPu]

theorem pairRevPu_succ (r : ℕ) (y : ℕ → G) (n : ℕ) :
    pairRevPu r y (n + 1) = pairRevPu r y n * y ((n + r - 1) % r) := by
  simp [pairRevPu, List.range_succ]

theorem pairRevCyc_succ (r : ℕ) (y : ℕ → G) (n : ℕ) :
    pairRevCyc r y (n + 1) = pairRevCyc r y n * y (n % r) := by
  simp [pairRevCyc, List.range_succ]

/-- `P(n + 1) = y_(r-1) (y_0 ⋯ y_(n-1))` (cyclic). -/
theorem pairRevPu_succ_eq {r : ℕ} (hr : 1 ≤ r) (y : ℕ → G) (n : ℕ) :
    pairRevPu r y (n + 1) = y (r - 1) * pairRevCyc r y n := by
  induction n with
  | zero =>
    simp only [pairRevPu_succ, pairRevPu_zero, one_mul, pairRevCyc, List.range_zero,
      List.map_nil, List.prod_nil, mul_one, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega)]
  | succ n ih =>
    rw [pairRevPu_succ, ih, pairRevCyc_succ, mul_assoc,
      show n + 1 + r - 1 = n + r by omega, Nat.add_mod_right]

/-- `P(n)` for `n ≤ r - 1`: `y_(r-1) y_0 ⋯ y_(n-2)`. -/
theorem pairRevPu_succ_low {r : ℕ} (hr : 1 ≤ r) (y : ℕ → G) (n : ℕ) (hn : n ≤ r) :
    pairRevPu r y (n + 1) = y (r - 1) * pairRevAsc y 0 n := by
  rw [pairRevPu_succ_eq hr]
  congr 1
  refine congrArg List.prod (List.map_congr_left fun t ht ↦ ?_)
  rw [Nat.zero_add, Nat.mod_eq_of_lt (by have := List.mem_range.1 ht; omega)]

/-- The cyclic product is `r`-periodic up to the full product: `P(n + r) = P(r) P(n)`. -/
theorem pairRevPu_add_r (r : ℕ) (y : ℕ → G) (n : ℕ) :
    pairRevPu r y (r + n) = pairRevPu r y r * pairRevPu r y n := by
  rw [pairRevPu, List.range_add, List.map_append, List.prod_append, List.map_map]
  congr 1
  refine congrArg List.prod (List.map_congr_left fun i _ ↦ ?_)
  simp only [Function.comp_apply, show r + i + r - 1 = i + r - 1 + r by omega, Nat.add_mod_right]

/-- The rounds telescope. -/
theorem descProd_pairRevRound (r : ℕ) (y : ℕ → G) (a n : ℕ) :
    descProd (pairRevRound r y) a n = pairRevPu r y (a + n) * (pairRevPu r y a)⁻¹ := by
  induction n with
  | zero => simp [descProd_zero_rl]
  | succ n ih =>
    rw [descProd_succ_top_rl, ih, pairRevRound, ← Nat.add_assoc]
    group

/-- The first round is `y_(r-1)`. -/
theorem pairRevRound_zero {r : ℕ} (hr : 1 ≤ r) (y : ℕ → G) : pairRevRound r y 0 = y (r - 1) := by
  rw [pairRevRound, pairRevPu_succ_low hr y 0 (by omega), pairRevPu_zero, pairRevAsc_zero]
  group

/-! ### The torus relation and the climbs -/

/-- The torus relation of the rotated tuple: `P(s) = y_0 ⋯ y_(s-1)` and
`u_i = P(s) u_(i+s) P(s)⁻¹`. -/
theorem pairRevPu_torus {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹) :
    pairRevPu r y s = pairRevCyc r y s ∧ ∀ i, y ((i + r - 1) % r) =
      pairRevPu r y s * y ((i + s + r - 1) % r) * (pairRevPu r y s)⁻¹ := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have h1 := hy (r - 1) (by omega)
  rw [show (r - 1 + (s' + 1)) % r = s' % r by
      rw [show r - 1 + (s' + 1) = s' + r by omega, Nat.add_mod_right], pairRevCyc_succ] at h1
  have hP : pairRevPu r y (s' + 1) = pairRevCyc r y (s' + 1) := by
    rw [pairRevPu_succ_eq hr, pairRevCyc_succ, h1]
    group
  refine ⟨hP, fun i ↦ ?_⟩
  rw [hP, hy _ (Nat.mod_lt _ (by omega))]
  congr 3
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show i + r - 1 + (s' + 1) = i + (s' + 1) + r - 1
    by omega]

/-- The products of the last rounds: `P(s) P(s - k)⁻¹ = u_(r-k) ⋯ u_(r-1)` for `k ≤ r - 1`. -/
theorem pairRevPu_climb {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (k : ℕ) (hkr : k ≤ r) (hks : k ≤ s) :
    pairRevPu r y s * (pairRevPu r y (s - k))⁻¹ =
      pairRevAsc (fun i ↦ y ((i + r - 1) % r)) (r - k) k := by
  obtain ⟨-, hT⟩ := pairRevPu_torus hr hs y hy
  set P := pairRevPu r y s with hPdef
  set W := pairRevAsc (fun i ↦ y ((i + r - 1) % r)) (r - k) k with hW
  have hsplit : P = pairRevPu r y (s - k) * pairRevAsc (fun i ↦ y ((i + r - 1) % r)) (s - k) k := by
    rw [hPdef, pairRevPu, show s = s - k + k by omega, List.range_add, List.map_append,
      List.prod_append, List.map_map, show s - k + k - k = s - k by omega]
    rfl
  have hconj : ∀ n, n ≤ k → pairRevAsc (fun i ↦ y ((i + r - 1) % r)) (s - k) n =
      P⁻¹ * pairRevAsc (fun i ↦ y ((i + r - 1) % r)) (r - k) n * P := by
    intro n hn
    induction n with
    | zero => simp [pairRevAsc_zero]
    | succ n ih =>
      rw [pairRevAsc_succ, ih (by omega), pairRevAsc_succ, hT (r - k + n),
        show (r - k + n + s + r - 1) % r = (s - k + n + r - 1) % r by
          rw [show r - k + n + s + r - 1 = s - k + n + r - 1 + r by omega, Nat.add_mod_right]]
      group
  rw [hconj k le_rfl, ← hW] at hsplit
  have hQ : pairRevPu r y (s - k) = W⁻¹ * P := by
    calc pairRevPu r y (s - k) = pairRevPu r y (s - k) * (P⁻¹ * W * P) * (P⁻¹ * W * P)⁻¹ := by
          group
      _ = W⁻¹ * P := by rw [← hsplit]; group
  rw [hQ]
  group

/-! ### The loops by position -/

section Loops

variable {r s : ℕ}

/-- The arithmetic of an admissible pair: `s ≤ c`, `r + 1 ≤ s` and `E + s + r = c + 3`. -/
theorem pairRev_arith (h : IsTorusPair r s) :
    2 ≤ r ∧ r + 1 ≤ s ∧ s ≤ pairC r s ∧ pairRunDown r s + s + r = pairC r s + 3 := by
  obtain ⟨hr, hrs, -⟩ := h
  obtain ⟨a, rfl⟩ : ∃ a, r = a + 2 := ⟨r - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, s = b + 1 := ⟨s - 1, by omega⟩
  simp only [pairC, pairRunDown, Nat.add_sub_cancel]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [show a + 2 - 1 = a + 1 by omega]
    nlinarith
  · rw [show a + 2 - 1 = a + 1 by omega]
    ring

/-- The position of `B` is `2c - s - r ≥ r - 1`. -/
theorem pairRev_idxB (h : IsTorusPair r s) :
    pairIdxB r s + s + r = 2 * pairC r s ∧ r - 1 ≤ pairIdxB r s := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairRev_arith h
  have hE1 : 1 ≤ pairRunDown r s := by unfold pairRunDown; omega
  simp only [pairIdxB]
  omega

theorem pairRevLoop_A (y : ℕ → G) (H : G) (q : ℕ) (hq : q < r - 2) :
    pairRevLoop r s y H q = (y q)⁻¹ := by
  simp only [pairRevLoop, hq, ite_true]

theorem pairRevLoop_run (y : ℕ → G) (H : G) (q : ℕ) (h1 : r - 2 ≤ q)
    (h2 : q < pairIdxB r s) : pairRevLoop r s y H q = (pairRevRound r y (s - 1))⁻¹ := by
  simp only [pairRevLoop, show ¬q < r - 2 by omega, h2, ite_true, ite_false]

theorem pairRevLoop_B (h : IsTorusPair r s) (y : ℕ → G) (H : G) :
    pairRevLoop r s y H (pairIdxB r s) = (y (r - 2))⁻¹ := by
  have := pairRev_idxB h
  obtain ⟨hr, hrs, hc, hE⟩ := pairRev_arith h
  simp only [pairRevLoop, show ¬pairIdxB r s < r - 2 by omega, lt_irrefl, ite_true, ite_false]

theorem pairRevLoop_R (h : IsTorusPair r s) (y : ℕ → G) (H : G) (t : ℕ) (ht : t ≤ s - 1) :
    pairRevLoop r s y H (pairIdxR r s t) = pairRevRound r y t := by
  have := pairRev_idxB h
  obtain ⟨hr, hrs, hc, hE⟩ := pairRev_arith h
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · simp only [pairIdxR, ite_true, pairRevLoop, show ¬pairIdxB r s + 1 < r - 2 by omega,
      show ¬pairIdxB r s + 1 < pairIdxB r s by omega, show pairIdxB r s + 1 ≠ pairIdxB r s by
      omega, ite_true, ite_false]
  · simp only [pairIdxR, show t ≠ 0 by omega, ite_false, pairRevLoop,
      show ¬pairIdxB r s + 2 + t < r - 2 by omega, show ¬pairIdxB r s + 2 + t < pairIdxB r s by
      omega, show pairIdxB r s + 2 + t ≠ pairIdxB r s by omega,
      show pairIdxB r s + 2 + t ≠ pairIdxB r s + 1 by omega,
      show pairIdxB r s + 2 + t ≠ pairIdxB r s + 2 by omega,
      show pairIdxB r s + 2 + t ≤ pairIdxB r s + s + 1 by omega, ite_true]
    congr 1
    omega

theorem pairRevLoop_H1 (h : IsTorusPair r s) (y : ℕ → G) (H : G) :
    pairRevLoop r s y H (pairIdxH1 r s) = H := by
  have := pairRev_idxB h
  obtain ⟨hr, hrs, hc, hE⟩ := pairRev_arith h
  simp only [pairIdxH1, pairRevLoop, show ¬pairIdxB r s + 2 < r - 2 by omega,
    show ¬pairIdxB r s + 2 < pairIdxB r s by omega, show pairIdxB r s + 2 ≠ pairIdxB r s by omega,
    show pairIdxB r s + 2 ≠ pairIdxB r s + 1 by omega, ite_true, ite_false]

theorem pairRevLoop_C (h : IsTorusPair r s) (y : ℕ → G) (H : G) :
    pairRevLoop r s y H (pairIdxC r s) = (pairRevRound r y 0)⁻¹ := by
  have := pairRev_idxB h
  obtain ⟨hr, hrs, hc, hE⟩ := pairRev_arith h
  simp only [pairIdxC, pairRevLoop, show ¬pairIdxB r s + s + 2 < r - 2 by omega,
    show ¬pairIdxB r s + s + 2 < pairIdxB r s by omega,
    show pairIdxB r s + s + 2 ≠ pairIdxB r s by omega,
    show pairIdxB r s + s + 2 ≠ pairIdxB r s + 1 by omega,
    show pairIdxB r s + s + 2 ≠ pairIdxB r s + 2 by omega,
    show ¬pairIdxB r s + s + 2 ≤ pairIdxB r s + s + 1 by omega, ite_true, ite_false]

theorem pairRevLoop_Dp (h : IsTorusPair r s) (y : ℕ → G) (H : G) (j : ℕ) (hj : j < r - 2) :
    pairRevLoop r s y H (pairIdxDp r s j) = y (r - 3 - j) := by
  have := pairRev_idxB h
  obtain ⟨hr, hrs, hc, hE⟩ := pairRev_arith h
  simp only [pairIdxDp, pairRevLoop, show ¬pairIdxB r s + s + 3 + j < r - 2 by omega,
    show ¬pairIdxB r s + s + 3 + j < pairIdxB r s by omega,
    show pairIdxB r s + s + 3 + j ≠ pairIdxB r s by omega,
    show pairIdxB r s + s + 3 + j ≠ pairIdxB r s + 1 by omega,
    show pairIdxB r s + s + 3 + j ≠ pairIdxB r s + 2 by omega,
    show ¬pairIdxB r s + s + 3 + j ≤ pairIdxB r s + s + 1 by omega,
    show pairIdxB r s + s + 3 + j ≠ pairIdxB r s + s + 2 by omega,
    show pairIdxB r s + s + 3 + j ≤ 2 * pairC r s by omega, ite_true, ite_false]
  congr 1
  omega

theorem pairRevLoop_H2 (h : IsTorusPair r s) (y : ℕ → G) (H : G) :
    pairRevLoop r s y H (pairIdxH2 r s) = H⁻¹ := by
  have := pairRev_idxB h
  obtain ⟨hr, hrs, hc, hE⟩ := pairRev_arith h
  simp only [pairIdxH2, pairRevLoop, show ¬2 * pairC r s + 1 < r - 2 by omega,
    show ¬2 * pairC r s + 1 < pairIdxB r s by omega,
    show 2 * pairC r s + 1 ≠ pairIdxB r s by omega,
    show 2 * pairC r s + 1 ≠ pairIdxB r s + 1 by omega,
    show 2 * pairC r s + 1 ≠ pairIdxB r s + 2 by omega,
    show ¬2 * pairC r s + 1 ≤ pairIdxB r s + s + 1 by omega,
    show 2 * pairC r s + 1 ≠ pairIdxB r s + s + 2 by omega,
    show ¬2 * pairC r s + 1 ≤ 2 * pairC r s by omega, ite_true, ite_false]

/-- The left climbs `A_(n-1) ⋯ A_0 = (y_0 ⋯ y_(n-1))⁻¹`. -/
theorem pairRevLoop_Aprod (y : ℕ → G) (H : G) (n : ℕ)
    (hn : n ≤ r - 2) : descProd (pairRevLoop r s y H) 0 n = (pairRevAsc y 0 n)⁻¹ := by
  rw [← descProd_inv_rl]
  exact descProd_congr_rl _ _ _ _ _ fun i hi ↦ pairRevLoop_A (s := s) y H _ (by omega)

/-- The right descents `D'_(r-3) ⋯ D'_(r-2-n) = y_0 ⋯ y_(n-1)`. -/
theorem pairRevLoop_Dprod (h : IsTorusPair r s) (y : ℕ → G) (H : G) (a n : ℕ)
    (han : a + n ≤ r - 2) :
    descProd (fun j ↦ pairRevLoop r s y H (pairIdxDp r s j)) a n = pairRevAsc y (r - 2 - a - n) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [descProd_zero_rl, pairRevAsc_zero]
  rw [descProd_congr_rl _ (fun j ↦ y (r - 3 - j)) a a n fun i hi ↦
    pairRevLoop_Dp h y H _ (by omega), descProd_rev_rl y (r - 3) a n (by omega),
    show r - 3 + 1 - a - n = r - 2 - a - n by omega]

/-- The rounds by position telescope. -/
theorem pairRevLoop_Rprod (h : IsTorusPair r s) (y : ℕ → G) (H : G) (a n : ℕ)
    (han : a + n ≤ s) :
    descProd (fun u ↦ pairRevLoop r s y H (pairIdxR r s u)) a n =
      pairRevPu r y (a + n) * (pairRevPu r y a)⁻¹ := by
  rw [← descProd_pairRevRound]
  exact descProd_congr_rl _ _ _ _ _ fun i hi ↦ pairRevLoop_R h y H _ (by omega)

end Loops

/-- The prescribed loops satisfy the gap relations of `pairBlocks r s` as soon as `y` satisfies
the torus relation (`y` fixed by `(σ_0 ⋯ σ_(r-2))^s`, by `braidRun_torusPairWord_fst`). -/
theorem pairGapRels_pairRevLoop {r s : ℕ} (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (H : G) : PairGapRels r s (pairRevLoop r s y H) := by
  obtain ⟨hr, hrs, hc, hE⟩ := pairRev_arith h
  have hB := pairRev_idxB h
  have hA := pairRevLoop_Aprod (s := s) y H (r - 2) le_rfl
  have hD := pairRevLoop_Dprod h y H 0 (r - 2) (by omega)
  rw [show r - 2 - 0 - (r - 2) = 0 by omega] at hD
  have hPr : pairRevPu r y r = y (r - 1) * pairRevAsc y 0 (r - 1) := by
    rw [show r = r - 1 + 1 by omega, pairRevPu_succ_low (by omega) y _ (by omega)]
    simp
  have hR0 : pairRevRound r y 0 = y (r - 1) := pairRevRound_zero (by omega) y
  have hAB : (y (r - 2))⁻¹ * (pairRevAsc y 0 (r - 2))⁻¹ = (pairRevAsc y 0 (r - 1))⁻¹ := by
    rw [show r - 1 = r - 2 + 1 by omega, pairRevAsc_succ, mul_inv_rev, Nat.zero_add]
  refine ⟨fun n hn1 hn2 ↦ ?_, fun n hn1 hn2 ↦ ?_, fun t ht1 ht2 ↦ ?_, fun t ht ↦ ?_,
    fun t ht1 ht2 ↦ ?_, ?_⟩
  · -- bottom levels
    rw [pairRevLoop_Dprod h y H _ _ (by omega), pairRevLoop_Aprod (s := s) y H n hn2,
      show r - 2 - (r - 2 - n) - n = 0 by omega, mul_inv_cancel]
  · -- run levels
    have hidx : r - 2 ≤ pairIdxRun r s n ∧ pairIdxRun r s n < pairIdxB r s := by
      unfold pairIdxRun
      simp only [pairIdxB] at hB ⊢
      split_ifs <;> omega
    rw [hD, hA, pairRevLoop_R h y H _ (by omega), pairRevLoop_run y H _ hidx.1 hidx.2]
    group
  · -- climb levels: `P(s) P(t + 1 - r)⁻¹ = y_(t-s) ⋯ y_(r-2)`
    rw [pairRevLoop_Dprod h y H _ _ (by omega), pairRevLoop_Rprod h y H _ _ (by omega),
      pairRevLoop_B h, hA, show r - 2 - (s + r - 2 - t) - (t - s) = 0 by omega,
      show t + 1 - r + (s + r - 1 - t) = s by omega,
      show t + 1 - r = s - (s + r - 1 - t) by omega,
      pairRevPu_climb (by omega) (by omega) y hy _ (by omega) (by omega), mul_assoc, hAB]
    have hW : pairRevAsc (fun i ↦ y ((i + r - 1) % r)) (r - (s + r - 1 - t)) (s + r - 1 - t) =
        pairRevAsc y (t - s) (s + r - 1 - t) := by
      refine congrArg List.prod (List.map_congr_left fun i hi ↦ ?_)
      have := List.mem_range.1 hi
      dsimp only
      rw [show r - (s + r - 1 - t) + i + r - 1 = t - s + i + r by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    have hsum : pairRevAsc y 0 (t - s) * pairRevAsc y (t - s) (s + r - 1 - t) = pairRevAsc y 0 (r - 1) := by
      rw [show r - 1 = t - s + (s + r - 1 - t) by omega, pairRevAsc_add, Nat.zero_add]
    rw [hW, hsum, mul_inv_cancel]
  · -- lower staircase levels
    rw [pairRevLoop_C h, pairRevLoop_Rprod h y H _ _ (by omega), pairRevLoop_Aprod (s := s) y H t ht,
      Nat.zero_add, pairRevPu_zero, inv_one, mul_one,
      pairRevPu_succ_low (by omega) y t (by omega), hR0]
    group
  · -- upper staircase levels
    rw [pairRevLoop_C h, pairRevLoop_Rprod h y H _ _ (by omega), pairRevLoop_B h, hA,
      show t + 1 - r + r = r + (t + 1 - r) by omega, pairRevPu_add_r, hPr, hR0, mul_assoc,
      mul_assoc, hAB]
    group
  · -- the Hopf level
    rw [pairRevLoop_H1 h, pairRevLoop_H2 h, inv_mul_cancel]

/-! ### The companion tuple -/

/-- The staircase window of the prescribed loops: `w_n = Q⁻¹ y_(r-1-n) Q` with
`Q = y_(r-n) ⋯ y_(r-2)`, for `2 ≤ n ≤ r - 1`. -/
private theorem pairWin_pairRevLoop {r s : ℕ} (h : IsTorusPair r s) (y : ℕ → G) (H : G) (n : ℕ)
    (hn1 : 2 ≤ n) (hn2 : n ≤ r - 1) :
    pairWin r s (pairRevLoop r s y H) n =
      (pairRevAsc y (r - n) (n - 1))⁻¹ * y (r - 1 - n) * pairRevAsc y (r - n) (n - 1) := by
  have hQ : descProd (pairRevLoop r s y H) (r - n) (n - 2) = (pairRevAsc y (r - n) (n - 2))⁻¹ := by
    rw [← descProd_inv_rl]
    exact descProd_congr_rl _ _ _ _ _ fun i hi ↦ pairRevLoop_A (s := s) y H _ (by omega)
  have hsplit : pairRevAsc y (r - n) (n - 1) = pairRevAsc y (r - n) (n - 2) * y (r - 2) := by
    rw [show n - 1 = n - 2 + 1 by omega, pairRevAsc_succ, show r - n + (n - 2) = r - 2 by omega]
  simp only [pairWin, show n ≠ 0 by omega, show n ≠ 1 by omega, ite_false]
  rw [pairRevLoop_B h, hQ, pairRevLoop_A (s := s) y H _ (by omega), hsplit,
    show r - 1 - n = r - 1 - n from rfl]
  group

/-- The prefix products of the window: `w_1 ⋯ w_m = y_(r-1-m) ⋯ y_(r-2)`. -/
private theorem pairWin_prefix_pairRevLoop {r s : ℕ} (h : IsTorusPair r s) (y : ℕ → G) (H : G)
    (m : ℕ) (hm : m ≤ r - 1) :
    ((List.range m).map fun i ↦ pairWin r s (pairRevLoop r s y H) (i + 1)).prod =
      pairRevAsc y (r - 1 - m) m := by
  have hr := h.1
  induction m with
  | zero => simp [pairRevAsc_zero]
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih (by omega), List.map_singleton,
      List.prod_singleton]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp only [pairRevAsc_zero, Nat.zero_add, one_mul, pairWin, one_ne_zero, ite_true, ite_false,
        pairRevLoop_B h, inv_inv]
      rw [show r - 1 - 1 = r - 2 by omega, show (1 : ℕ) = 0 + 1 from rfl, pairRevAsc_succ, pairRevAsc_zero,
        one_mul, Nat.add_zero]
    · rw [pairWin_pairRevLoop h y H (m + 1) (by omega) (by omega),
        show r - (m + 1) = r - 1 - m by omega, show m + 1 - 1 = m by omega,
        show r - 1 - (m + 1) = r - 1 - m - 1 by omega]
      rw [show pairRevAsc y (r - 1 - m - 1) (m + 1) = y (r - 1 - m - 1) * pairRevAsc y (r - 1 - m) m by
        rw [pairRevAsc_succ_bot, show r - 1 - m - 1 + 1 = r - 1 - m by omega]]
      group

/-- The companion tuple of the prescribed loops is `y`. -/
theorem pairCompFun_pairRevLoop {r s : ℕ} (h : IsTorusPair r s) (y : ℕ → G) (H : G) (k : ℕ)
    (hk : k < r) : pairCompFun r s (pairRevLoop r s y H) k = y k := by
  have hr := h.1
  rw [pairCompFun, pairWin_prefix_pairRevLoop h y H _ (by omega)]
  rcases Nat.lt_or_ge k (r - 2) with hk2 | hk2
  · rw [pairWin_pairRevLoop h y H (r - 1 - k) (by omega) (by omega),
      show r - (r - 1 - k) = k + 1 by omega, show r - 1 - k - 1 = r - 2 - k by omega,
      show r - 1 - (r - 2 - k) = k + 1 by omega, show r - 1 - (r - 1 - k) = k by omega]
    group
  · rcases Nat.lt_or_ge k (r - 1) with hk1 | hk1
    · rw [show r - 2 - k = 0 by omega, show r - 1 - k = 1 by omega]
      simp only [pairRevAsc_zero, one_mul, inv_one, mul_one, pairWin, one_ne_zero, ite_true,
        ite_false, pairRevLoop_B h, inv_inv]
      congr 1
      omega
    · rw [show r - 2 - k = 0 by omega, show r - 1 - k = 0 by omega]
      simp only [pairRevAsc_zero, one_mul, inv_one, mul_one, pairWin, ite_true]
      rw [pairRevLoop_R h y H 0 (by omega), pairRevRound_zero (by omega)]
      congr 1
      omega

end AJConjecture
