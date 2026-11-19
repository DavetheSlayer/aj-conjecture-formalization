import Mathlib
import AJConjecture.SkeinPartialTrace
import AJConjecture.SkeinPlaceAppend

/-!
# Properties of the partial quantum trace

The quantum trace factors through the partial trace, partial traces compose, and the partial
trace is a bimodule map over the operators on the factors that are kept:
`ptr((B ⊗ 1) A) = B ptr(A)`, `ptr(A (B ⊗ 1)) = ptr(A) B`. All four are rearrangements of finite
sums, using the bijection between the states of `V^{⊗ n}` and pairs of states of `V^{⊗ k}` and
`V^{⊗ (n-k)}`.
-/

namespace AJConjecture

/-- The value of a concatenation of states, by the position. -/
theorem append_apply_dite {m n : ℕ} (a : Fin m → Bool) (b : Fin n → Bool)
    (x : Fin (m + n)) :
    Fin.append a b x = if h : (x : ℕ) < m then a ⟨x, h⟩ else b ⟨x - m, by omega⟩ := by
  induction x using Fin.addCases with
  | left x => simp
  | right x => simp

/-- Proves an equality between two values of states that are defined by cases on the
position. -/
local macro "state_cases_ptrTailBasic" : tactic =>
  `(tactic| (simp only [append_apply_dite, Fin.val_cast]
             split_ifs <;> first | rfl | (exfalso; omega) |
               (congr 1; exact Fin.ext (by dsimp only; omega))))

/-- A sum over the states of `m + n` factors is a double sum. -/
theorem sum_append_states {m n : ℕ}
    (f : (Fin (m + n) → Bool) → RatFunc ℚ) :
    ∑ c, f c = ∑ a : Fin m → Bool, ∑ b : Fin n → Bool, f (Fin.append a b) :=
  (Fintype.sum_equiv (Fin.appendEquiv m n) (fun p ↦ f (Fin.append p.1 p.2)) f
    (fun _ ↦ rfl)).symm.trans (Fintype.sum_prod_type' fun a b ↦ f (Fin.append a b))

/-- The weight of a concatenation is the product of the weights. -/
theorem prod_skWeightEntry_append {m n : ℕ} (a : Fin m → Bool)
    (b : Fin n → Bool) :
    ∏ x, skWeightEntry (Fin.append a b x) =
      (∏ x, skWeightEntry (a x)) * ∏ x, skWeightEntry (b x) := by
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The entries of a partial trace, with the number of traced factors as a parameter. -/
theorem ptrTail_apply_of_eq (k n r : ℕ) (hn : n = k + r) (A : SkMat n n)
    (a b : Fin k → Bool) :
    ptrTail k n A a b = ∑ s : Fin r → Bool, (∏ x, skWeightEntry (s x)) *
      A (fun j ↦ if h : (j : ℕ) < k then a ⟨j, h⟩ else s ⟨j - k, by omega⟩)
        (fun j ↦ if h : (j : ℕ) < k then b ⟨j, h⟩ else s ⟨j - k, by omega⟩) := by
  obtain rfl : r = n - k := by omega
  rfl

/-- The entries of a partial trace on concatenated states. -/
theorem ptrTail_append_apply (k r : ℕ) (A : SkMat (k + r) (k + r))
    (a b : Fin k → Bool) :
    ptrTail k (k + r) A a b =
      ∑ s : Fin r → Bool, (∏ x, skWeightEntry (s x)) * A (Fin.append a s) (Fin.append b s) := by
  rw [ptrTail_apply_of_eq k (k + r) r rfl]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  congr 2 <;> funext x <;> rw [append_apply_dite]

/-- The entries of a placement, with the ambient sizes as parameters. -/
theorem skPlace_apply_of_eq {n n' : ℕ} (i r : ℕ) {k l : ℕ} (A : SkMat k l)
    (hn : n = i + k + r) (hn' : n' = i + l + r) (a : Fin n → Bool) (b : Fin n' → Bool)
    (a₁ b₁ : Fin i → Bool) (a₂ : Fin k → Bool) (b₂ : Fin l → Bool) (a₃ b₃ : Fin r → Bool)
    (ha : ∀ x, a x = Fin.append (Fin.append a₁ a₂) a₃ (Fin.cast hn x))
    (hb : ∀ x, b x = Fin.append (Fin.append b₁ b₂) b₃ (Fin.cast hn' x)) :
    skPlace n n' i A a b = if a₁ = b₁ ∧ a₃ = b₃ then A a₂ b₂ else 0 := by
  subst hn hn'
  obtain rfl : a = Fin.append (Fin.append a₁ a₂) a₃ := funext ha
  obtain rfl : b = Fin.append (Fin.append b₁ b₂) b₃ := funext hb
  exact skPlace_append_apply i r A a₁ b₁ a₂ b₂ a₃ b₃

/-- The entries of a matrix placed at the position `0`. -/
private theorem skPlace_zero_append_apply_ptrTailBasic (r : ℕ) {k l : ℕ} (A : SkMat k l)
    (a₂ : Fin k → Bool) (b₂ : Fin l → Bool) (a₃ b₃ : Fin r → Bool) :
    skPlace (k + r) (l + r) 0 A (Fin.append a₂ a₃) (Fin.append b₂ b₃) =
      if a₃ = b₃ then A a₂ b₂ else 0 := by
  rw [skPlace_apply_of_eq 0 r A (by omega) (by omega) (Fin.append a₂ a₃)
    (Fin.append b₂ b₃) Fin.elim0 Fin.elim0 a₂ b₂ a₃ b₃
    (fun x ↦ by state_cases_ptrTailBasic) (fun x ↦ by state_cases_ptrTailBasic)]
  simp

/-- The quantum trace as a weighted sum of diagonal entries. -/
private theorem qtr_eq_sum_ptrTailBasic (n : ℕ) (A : SkMat n n) :
    qtr n A = ∑ c, (∏ x, skWeightEntry (c x)) * A c c := by
  rw [qtr, Matrix.trace, skWeight]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.diagonal_mul]

/-- The quantum trace is the quantum trace of the partial trace. -/
theorem qtr_eq_qtr_ptrTail (k n : ℕ) (h : k ≤ n) (A : SkMat n n) :
    qtr n A = qtr k (ptrTail k n A) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + r := ⟨n - k, by omega⟩
  rw [qtr_eq_sum_ptrTailBasic, qtr_eq_sum_ptrTailBasic, sum_append_states]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [ptrTail_append_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [prod_skWeightEntry_append, mul_assoc]

/-- Tracing nothing does nothing. -/
theorem ptrTail_self (n : ℕ) (A : SkMat n n) : ptrTail n n A = A := by
  ext a b
  rw [ptrTail_apply_of_eq n n 0 rfl, Fintype.sum_unique]
  simp

/-- Partial traces compose. -/
theorem ptrTail_ptrTail (j k n : ℕ) (hjk : j ≤ k) (hkn : k ≤ n) (A : SkMat n n) :
    ptrTail j k (ptrTail k n A) = ptrTail j n A := by
  obtain ⟨p, rfl⟩ : ∃ p, k = j + p := ⟨k - j, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, n = j + p + q := ⟨n - (j + p), by omega⟩
  ext a b
  rw [ptrTail_append_apply,
    ptrTail_apply_of_eq j (j + p + q) (p + q) (by omega),
    sum_append_states]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [ptrTail_append_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  have e : ∀ c : Fin j → Bool, (fun x : Fin (j + p + q) ↦ if h : (x : ℕ) < j then c ⟨x, h⟩ else
      Fin.append s u ⟨x - j, by omega⟩) = Fin.append (Fin.append c s) u := fun c ↦ by
    funext x
    state_cases_ptrTailBasic
  rw [prod_skWeightEntry_append, mul_assoc, e a, e b]

/-- An operator on the kept factors comes out of the partial trace on the left. -/
theorem ptrTail_skPlace_mul (k n : ℕ) (h : k ≤ n) (B : SkMat k k) (A : SkMat n n) :
    ptrTail k n (skPlace n n 0 B * A) = B * ptrTail k n A := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + r := ⟨n - k, by omega⟩
  ext a b
  simp only [ptrTail_append_apply, Matrix.mul_apply, sum_append_states,
    skPlace_zero_append_apply_ptrTailBasic, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  ring

/-- An operator on the kept factors comes out of the partial trace on the right. -/
theorem ptrTail_mul_skPlace (k n : ℕ) (h : k ≤ n) (A : SkMat n n) (B : SkMat k k) :
    ptrTail k n (A * skPlace n n 0 B) = ptrTail k n A * B := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + r := ⟨n - k, by omega⟩
  ext a b
  simp only [ptrTail_append_apply, Matrix.mul_apply, sum_append_states,
    skPlace_zero_append_apply_ptrTailBasic, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  ring

end AJConjecture
