import Mathlib
import AJFamily.Skein.TorusWord

/-!
# The strand permutation of the family word

`strandPerm_whiteheadTorusWord`: the strand permutation of `whiteheadTorusWord k` is the explicit
map `whiteheadTorusPermNat k`. Each band `b(i, j)` acts as the transposition of `i` and `j`.
-/

open Polynomial LaurentPolynomial

noncomputable section

namespace AJConjecture

/-- The transposition of `a` and `b` as a function on `ℕ`. -/
private def twpSwapNat (a b x : ℕ) : ℕ := if x = a then b else if x = b then a else x

/-- The strand permutation of a concatenation is the product. -/
private theorem twp_strandPerm_append (m : ℕ) (u v : BraidWord) :
    strandPerm m (u ++ v) = strandPerm m u * strandPerm m v := by
  simp only [strandPerm, List.map_append, List.prod_append]

/-- The value of a transposition of `Fin m`, as a natural number. -/
private theorem twp_swap_val (m a b : ℕ) (ha : a < m) (hb : b < m) (x : Fin m) :
    ((Equiv.swap (⟨a, ha⟩ : Fin m) ⟨b, hb⟩ x : Fin m) : ℕ) = twpSwapNat a b x := by
  unfold twpSwapNat
  rw [Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

/-- The value of an adjacent strand swap, as a natural number. -/
private theorem twp_strandSwap_val (m l : ℕ) (hl : l + 1 < m) (x : Fin m) :
    ((strandSwap m l x : Fin m) : ℕ) = twpSwapNat l (l + 1) x := by
  simp only [strandSwap, hl, ↓reduceDIte, twp_swap_val]

/-- The strand permutation of a one-letter word. -/
private theorem twp_strandPerm_single_val (m l : ℕ) (b : Bool) (hl : l + 1 < m) (x : Fin m) :
    ((strandPerm m [(l, b)] x : Fin m) : ℕ) = twpSwapNat l (l + 1) x := by
  simp only [strandPerm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact twp_strandSwap_val m l hl x

/-- Peeling one conjugating letter off each end of a band. -/
private theorem twp_surfaceBand_succ (i n : ℕ) :
    surfaceBand i (i + 1 + (n + 1)) =
      [(i + 1 + n, true)] ++ surfaceBand i (i + 1 + n) ++ [(i + 1 + n, false)] := by
  simp only [surfaceBand]
  rw [show i + 1 + (n + 1) - i - 1 = n + 1 by omega, show i + 1 + n - i - 1 = n by omega]
  have hr : (List.range (n + 1)).map (fun x ↦ (i + 1 + x, false)) =
      (List.range n).map (fun x ↦ (i + 1 + x, false)) ++ [(i + 1 + n, false)] := by
    rw [List.range_succ, List.map_append, List.map_singleton]
  have hl : (List.range (n + 1)).map (fun x ↦ (i + 1 + (n + 1) - 1 - x, true)) =
      (i + 1 + n, true) :: (List.range n).map (fun x ↦ (i + 1 + n - 1 - x, true)) := by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine List.cons_eq_cons.2 ⟨by simp, List.map_congr_left fun x _ ↦ ?_⟩
    simp only [Function.comp_apply, Prod.mk.injEq, and_true]
    omega
  rw [hr, hl]
  simp only [List.cons_append, List.nil_append, List.append_assoc]

/-- The band `b(i, i + 1 + n)` acts as the transposition of `i` and `i + 1 + n`. -/
private theorem twp_surfaceBand_val_aux (m i n : ℕ) (h : i + 1 + n < m) (x : Fin m) :
    ((strandPerm m (surfaceBand i (i + 1 + n)) x : Fin m) : ℕ) = twpSwapNat i (i + 1 + n) x := by
  induction n generalizing x with
  | zero =>
    have hw : surfaceBand i (i + 1 + 0) = [(i, true)] := by simp [surfaceBand]
    rw [hw, twp_strandPerm_single_val m i true (by omega)]
  | succ n ih =>
    rw [twp_surfaceBand_succ, twp_strandPerm_append, twp_strandPerm_append,
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, twp_strandPerm_single_val m _ _ (by omega),
      ih (by omega), twp_strandPerm_single_val m _ _ (by omega)]
    unfold twpSwapNat
    split_ifs <;> omega

/-- The strand permutation of the band `surfaceBand i j` is the transposition of `i` and `j`. -/
private theorem twp_surfaceBand_val (m i j : ℕ) (hij : i < j) (hj : j < m) (x : Fin m) :
    ((strandPerm m (surfaceBand i j) x : Fin m) : ℕ) = twpSwapNat i j x := by
  obtain ⟨n, rfl⟩ : ∃ n, j = i + 1 + n := ⟨j - i - 1, by omega⟩
  exact twp_surfaceBand_val_aux m i n hj x

/-- The strand permutation of the climb `σ_0 σ_1 ⋯ σ_{n-1}`. -/
private theorem twp_climb_val (m n : ℕ) (hn : n < m) (x : Fin m) :
    ((strandPerm m ((List.range n).map fun l ↦ (l, true)) x : Fin m) : ℕ) =
      if (x : ℕ) < n then (x : ℕ) + 1 else if (x : ℕ) = n then 0 else (x : ℕ) := by
  induction n generalizing x with
  | zero => simp [strandPerm]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, twp_strandPerm_append,
      Equiv.Perm.mul_apply, ih (by omega), twp_strandPerm_single_val m _ _ (by omega)]
    unfold twpSwapNat
    split_ifs <;> omega

/-- The strand permutation of the staircase `∏_{s < n} b(c - s, c + 2 - s)`. -/
private theorem twp_staircase_val (m c d n : ℕ) (hd : d = c + 2) (hn : n ≤ c + 1) (hm : d < m)
    (x : Fin m) :
    ((strandPerm m ((List.range n).flatMap fun s ↦ surfaceBand (c - s) (d - s)) x : Fin m) : ℕ) =
      if c + 3 - n ≤ (x : ℕ) ∧ (x : ℕ) ≤ c + 2 then (x : ℕ) - 2
      else if (x : ℕ) = c + 1 - n then (if n % 2 = 0 then c + 1 else c + 2)
      else if (x : ℕ) = c + 2 - n then (if n % 2 = 0 then c + 2 else c + 1)
      else (x : ℕ) := by
  subst hd
  induction n generalizing x with
  | zero =>
    simp only [List.range_zero, List.flatMap_nil, strandPerm, List.map_nil, List.prod_nil,
      Equiv.Perm.coe_one, id_eq]
    split_ifs <;> omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, twp_strandPerm_append,
      Equiv.Perm.mul_apply, ih (by omega), twp_surfaceBand_val m _ _ (by omega) (by omega)]
    unfold twpSwapNat
    split_ifs <;> omega

/-- The strand permutation of `whiteheadTorusWord k` as a function on indices (`a = 2k+1`):
`0 ↦ 2a-1`, `i ↦ i+1` (`1 ≤ i ≤ a-3`), `a-2 ↦ 2a-2`, `a-1 ↦ 2a`, `a ↦ 1`, `i ↦ i-2`
(`a+1 ≤ i ≤ 2a-1`), `2a ↦ 0`. -/
def whiteheadTorusPermNat (k i : ℕ) : ℕ :=
  if i = 0 then 4 * k + 1
  else if i ≤ 2 * k - 2 then i + 1
  else if i = 2 * k - 1 then 4 * k
  else if i = 2 * k then 4 * k + 2
  else if i = 2 * k + 1 then 1
  else if i ≤ 4 * k + 1 then i - 2
  else 0

set_option maxHeartbeats 800000 in
theorem strandPerm_whiteheadTorusWord (k : ℕ) (hk : 1 ≤ k) (i : Fin (4 * k + 3)) :
    ((strandPerm (4 * k + 3) (whiteheadTorusWord k) i : Fin (4 * k + 3)) : ℕ) =
      whiteheadTorusPermNat k i := by
  rw [whiteheadTorusWord]
  simp only [twp_strandPerm_append, Equiv.Perm.mul_apply]
  have e1 := twp_strandPerm_single_val (4 * k + 3) (4 * k + 1) false (by omega) i
  generalize strandPerm (4 * k + 3) [(4 * k + 1, false)] i = x1 at e1 ⊢
  have e2 := twp_surfaceBand_val (4 * k + 3) (2 * k) (4 * k + 1) (by omega) (by omega) x1
  generalize strandPerm (4 * k + 3) (surfaceBand (2 * k) (4 * k + 1)) x1 = x2 at e2 ⊢
  have e3 := twp_surfaceBand_val (4 * k + 3) 0 (2 * k + 1) (by omega) (by omega) x2
  generalize strandPerm (4 * k + 3) (surfaceBand 0 (2 * k + 1)) x2 = x3 at e3 ⊢
  have e4 := twp_staircase_val (4 * k + 3) (4 * k - 2) (4 * k) (2 * k - 1) (by omega) (by omega)
    (by omega) x3
  generalize strandPerm (4 * k + 3) ((List.range (2 * k - 1)).flatMap
    fun s ↦ surfaceBand (4 * k - 2 - s) (4 * k - s)) x3 = x4 at e4 ⊢
  have e5 := twp_strandPerm_single_val (4 * k + 3) (4 * k + 1) false (by omega) x4
  generalize strandPerm (4 * k + 3) [(4 * k + 1, false)] x4 = x5 at e5 ⊢
  have e6 := twp_surfaceBand_val (4 * k + 3) (4 * k - 1) (4 * k + 1) (by omega) (by omega) x5
  generalize strandPerm (4 * k + 3) (surfaceBand (4 * k - 1) (4 * k + 1)) x5 = x6 at e6 ⊢
  have e7 := twp_surfaceBand_val (4 * k + 3) (2 * k - 1) (4 * k) (by omega) (by omega) x6
  generalize strandPerm (4 * k + 3) (surfaceBand (2 * k - 1) (4 * k)) x6 = x7 at e7 ⊢
  rw [twp_climb_val (4 * k + 3) (2 * k - 1) (by omega)]
  have hi := i.isLt
  have h2 : (2 * k - 1) % 2 = 1 := by omega
  simp only [twpSwapNat, h2, one_ne_zero, ↓reduceIte] at e1 e2 e3 e4 e5 e6 e7
  unfold whiteheadTorusPermNat
  split_ifs <;> split_ifs at e1 <;> (try omega) <;> split_ifs at e2 <;> (try omega) <;>
    split_ifs at e3 <;> (try omega) <;> split_ifs at e4 <;> (try omega) <;>
    split_ifs at e5 <;> (try omega) <;> split_ifs at e6 <;> (try omega) <;>
    split_ifs at e7 <;> omega

end AJConjecture
