import Mathlib
import AJConjecture.ClaspAlgPochForms

/-!
# The eigenvalues of the turnback elements: recursion, vanishing, separation

Facts on `d_{j,n} = ∏_{i<j} (-[c-n-i][c+n+1-i] / [c-i]²)` (`AJConjecture.claspAlgTurnbackEigen`)
that
the spectral theory of the two-bundle algebra uses.

* Recursion: `d_{k+1,n} α_k = d_{k,n} (d_{1,n} - β_k)` with `α_k = [c-k]²/[c]²` and
  `β_k = -[k][2c+1-k]/[c]²`, the coefficients of `D_1 D_k = α_k D_{k+1} + β_k D_k`. After clearing
  the denominators it is `[a][b] - [k][a+b-k] = [a-k][b-k]` with `a = c - n`, `b = c + n + 1`, an
  identity of Laurent polynomials in `t`.
* `d_{j,n} ≠ 0` for `j + n ≤ c` (all quantum integers in the product have non-zero arguments,
  `AJConjecture.claspAlg_quantumInt_ne_zero`), and `d_{j,n} = 0` for `n ≤ c < j + n` (the factor
  `i = c - n` is `[0] = 0`).
* The eigenvalues `d_{1,n} = -[c-n][c+n+1]/[c]²`, `n ≤ c`, are pairwise distinct:
  `[c-n][c+n+1] (t²-t⁻²)² = t^(4c+2) + t^(-4c-2) - t^(4n+2) - t^(-4n-2)`, and the powers of `t` are
  linearly independent.
-/

namespace AJConjecture

/-- `[p+r][q+r] - [p][q] = [r][p+q+r]`. -/
theorem quantumInt_mul_shift_sub (p q r : ℤ) :
    quantumInt (p + r) * quantumInt (q + r) - quantumInt p * quantumInt q =
      quantumInt r * quantumInt (p + q + r) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hD := claspAlg_ratFuncX_sq_sub_ne_zero
  have hP : (RatFunc.X : RatFunc ℚ) ^ (2 * p) ≠ 0 := zpow_ne_zero _ hX
  have hQ : (RatFunc.X : RatFunc ℚ) ^ (2 * q) ≠ 0 := zpow_ne_zero _ hX
  have hR : (RatFunc.X : RatFunc ℚ) ^ (2 * r) ≠ 0 := zpow_ne_zero _ hX
  simp only [quantumInt, mul_add, neg_add, zpow_add₀ hX, zpow_neg]
  field_simp
  ring

/-- `d_{0,n} = 1`. -/
theorem turnbackEigen_zero (c n : ℕ) : claspAlgTurnbackEigen c 0 n = 1 :=
  Finset.prod_range_zero _

/-- The recursion of the eigenvalues, in the form given by `D_1 D_k = α_k D_{k+1} + β_k D_k`. -/
theorem turnbackEigen_succ_mul (c k n : ℕ) (hk : k < c) :
    claspAlgTurnbackEigen c (k + 1) n * (quantumInt ((c : ℤ) - k) ^ 2 / quantumInt (c : ℤ) ^ 2) =
      claspAlgTurnbackEigen c k n * (claspAlgTurnbackEigen c 1 n -
        -(quantumInt (k : ℤ) * quantumInt (2 * (c : ℤ) + 1 - k)) / quantumInt (c : ℤ) ^ 2) := by
  have hck : quantumInt ((c : ℤ) - k) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have hc : quantumInt (c : ℤ) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have key : quantumInt ((c : ℤ) - n) * quantumInt ((c : ℤ) + n + 1) -
      quantumInt ((c : ℤ) - n - k) * quantumInt ((c : ℤ) + n + 1 - k) =
        quantumInt (k : ℤ) * quantumInt (2 * (c : ℤ) + 1 - k) := by
    have h := quantumInt_mul_shift_sub ((c : ℤ) - n - k) ((c : ℤ) + n + 1 - k) k
    rw [show (c : ℤ) - n - k + k = (c : ℤ) - n from by ring,
      show (c : ℤ) + n + 1 - k + k = (c : ℤ) + n + 1 from by ring,
      show (c : ℤ) - n - k + ((c : ℤ) + n + 1 - k) + k = 2 * (c : ℤ) + 1 - k from by ring] at h
    exact h
  unfold claspAlgTurnbackEigen
  rw [Finset.prod_range_succ, Finset.prod_range_one]
  simp only [Nat.cast_zero, sub_zero]
  generalize (∏ i ∈ Finset.range k, (_ : RatFunc ℚ)) = P
  field_simp
  linear_combination P * key

/-- `d_{j,n} ≠ 0` for `j ≤ c - n`. -/
theorem turnbackEigen_ne_zero (c j n : ℕ) (h : j + n ≤ c) : claspAlgTurnbackEigen c j n ≠ 0 := by
  unfold claspAlgTurnbackEigen
  refine Finset.prod_ne_zero_iff.mpr fun i hi ↦ ?_
  have hi' : i < j := Finset.mem_range.mp hi
  have h1 : quantumInt ((c : ℤ) - n - i) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have h2 : quantumInt ((c : ℤ) + n + 1 - i) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have h3 : quantumInt ((c : ℤ) - i) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero h1 h2)) (pow_ne_zero 2 h3)

/-- `d_{j,n} = 0` for `j > c - n`. -/
theorem turnbackEigen_eq_zero (c j n : ℕ) (hn : n ≤ c) (h : c < j + n) :
    claspAlgTurnbackEigen c j n = 0 :=
  claspAlgTurnbackEigen_eq_zero c j n hn h

/-- The eigenvalues `d_{1,n}`, `n ≤ c`, of `D_1` are pairwise distinct. -/
theorem turnbackEigen_one_injective (c n n' : ℕ) (hn : n ≤ c) (hn' : n' ≤ c)
    (h : claspAlgTurnbackEigen c 1 n = claspAlgTurnbackEigen c 1 n') : n = n' := by
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · omega
  have hc : quantumInt (c : ℤ) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  unfold claspAlgTurnbackEigen at h
  rw [Finset.prod_range_one, Finset.prod_range_one] at h
  simp only [Nat.cast_zero, sub_zero] at h
  rw [div_left_inj₀ (pow_ne_zero 2 hc), neg_inj] at h
  have key := quantumInt_mul_shift_sub ((n' : ℤ) - c) ((c : ℤ) + n' + 1) ((n : ℤ) - n')
  rw [show (n' : ℤ) - c + ((n : ℤ) - n') = -((c : ℤ) - n) from by ring,
    show (c : ℤ) + n' + 1 + ((n : ℤ) - n') = (c : ℤ) + n + 1 from by ring,
    show (n' : ℤ) - c = -((c : ℤ) - n') from by ring,
    show -((c : ℤ) - n') + ((c : ℤ) + n' + 1) + ((n : ℤ) - n') = (n : ℤ) + n' + 1 from by ring,
    claspAlg_quantumInt_neg, claspAlg_quantumInt_neg, neg_mul, neg_mul, h, sub_self] at key
  have h2 : quantumInt ((n : ℤ) + n' + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have h3 : quantumInt ((n : ℤ) - n') = 0 := by
    rcases mul_eq_zero.mp key.symm with h3 | h3
    · exact h3
    · exact absurd h3 h2
  by_contra hne
  exact claspAlg_quantumInt_ne_zero (m := (n : ℤ) - n') (by omega) h3

end AJConjecture
