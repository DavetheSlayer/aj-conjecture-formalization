import Mathlib
import AJConjecture.QAlgSymbolPoly
import AJConjecture.QAlgWeylSymbol
import AJConjecture.QAlgInnerDerivativeBasic
import AJConjecture.QAlgMoebiusSubstMul

/-!
# The stationary pullback to first order (TwF, generic)

Source: revision 5, Section 5.2, eq. (physical-derivatives): `D_u = (A_*/D_*) ∂_J`,
`D_x = D_* ∂_K + (J² - 1)/D_* ∂_J`; Section 3.4 (the blocks are the pullbacks of the factors of
`Π_a` under `J = (x L + 1)/(L + x)`, `x = M²`).

`twfPullback n f` is `(L + x)^n f(x, J(L))` with `x = M²`, for `f ∈ ℤ[x][J]` of degree at most
`n` in `J`: the library's `moebiusSubst n f` followed by `x = M²`. The blocks are of this form:
`twistPoly k = twfPullback (2k) (symbolTwist k)` (`map_moebiusSubst_symbolTwist`),
`twistPolyNeg b = twfPullback (2b-1) (symbolTwistNeg b)` (by definition),
`zetaMoebiusM = twfPullback 2 symbolZeta`.

At a point `(m, l)` with `J (l + m²) = m² l + 1`:
* `evalIntPoint_twfPullback`: the value is `(l + m²)^n f(m², J)`;
* at a zero of `f`: `(l + m²)² ∂_L F = (l + m²)^n (m⁴ - 1) ∂_J f` and
  `(l + m²)² ∂_M F = 2m (l + m²)^n ((l + m²)² ∂_x f + (l² - 1) ∂_J f)`.
So `G`, `D` cross transversally in `(M, L)` exactly when their sources do in `(x, J)`:
`∂_L F ∂_M G - ∂_M F ∂_L G = 2m (l + m²)^(n+n'-2) (m⁴ - 1)(∂_J f ∂_x g - ∂_x f ∂_J g)`
(`twfPullback_jacobian`).

Here `evalIntPoint f x₀ J₀` evaluates `f ∈ ℤ[x][J]` at `x = x₀`, `J = J₀`; `derivative` is `∂_J`
(resp. `∂_L`) and `coeffDerivative` is `∂_x` (resp. `∂_M`).
Route: linearity in `f` reduces to `f = C c * X ^ k`, `k ≤ n`, where
`F = C (c.comp (X ^ 2)) * (C (X ^ 2) * X + 1) ^ k * (C (X ^ 2) + X) ^ (n - k)`; the derivations
`derivative`, `coeffDerivative` (= `innerDerivative`, `coeffDerivative_eq_innerDerivative`) obey
the Leibniz rule. Checked at random points for `n = 1, 2, 3, 5` (scratch
`check_generic_parts.py` (D)).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The stationary pullback `(L + x)^n f(x, (x L + 1)/(L + x))`, `x = M²`, of a polynomial
`f ∈ ℤ[x][J]` of degree at most `n` in `J`. -/
def twfPullback (n : ℕ) (f : ℤ[X][X]) : ℤ[X][X] :=
  (moebiusSubst n f).map (Polynomial.compRingHom (X ^ 2))

/-- Evaluation at a complex point `(m, l)`, as a ring homomorphism. -/
private def evalIntHomTwfMoebius (m l : ℂ) : ℤ[X][X] →+* ℂ :=
  (Polynomial.eval₂RingHom (Polynomial.evalRingHom m) l).comp
    (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℂ)))

/-- `evalIntPoint` is the evaluation homomorphism. -/
private theorem evalIntPoint_eq_twfMoebius (p : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint p m l = evalIntHomTwfMoebius m l p :=
  rfl

/-- The value of a polynomial constant in the outer variable. -/
private theorem evalIntHomTwfMoebius_C (m l : ℂ) (κ : ℤ[X]) :
    evalIntHomTwfMoebius m l (C κ) = (κ.map (Int.castRingHom ℂ)).eval m := by
  simp [evalIntHomTwfMoebius]

/-- The value of the outer variable. -/
private theorem evalIntHomTwfMoebius_X (m l : ℂ) : evalIntHomTwfMoebius m l X = l := by
  simp [evalIntHomTwfMoebius]

/-- The inner derivative of the outer variable vanishes. -/
private theorem innerDerivative_X_twfMoebius : innerDerivative (X : ℤ[X][X]) = 0 := by
  rw [← monomial_one_one_eq_X]
  simp [innerDerivative]

/-- The inner derivative of `1` vanishes. -/
private theorem innerDerivative_one_twfMoebius : innerDerivative (1 : ℤ[X][X]) = 0 := by
  rw [← C_1, innerDerivative_C, derivative_one, C_0]

/-- The power rule for the inner derivative. -/
private theorem innerDerivative_pow_twfMoebius (p : ℤ[X][X]) (n : ℕ) :
    innerDerivative (p ^ n) = C (n : ℤ[X]) * p ^ (n - 1) * innerDerivative p := by
  induction n with
  | zero =>
    rw [pow_zero, ← C_1, innerDerivative_C, derivative_one]
    simp
  | succ n ih =>
    rw [pow_succ, innerDerivative_mul, ih, Nat.add_sub_cancel]
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel, pow_succ p n]
      push_cast
      simp only [C_add, C_1]
      ring

/-- The stationary pullback is additive. -/
private theorem twfPullback_add_twfMoebius (n : ℕ) (f g : ℤ[X][X]) :
    twfPullback n (f + g) = twfPullback n f + twfPullback n g := by
  rw [twfPullback, moebiusSubst_add, Polynomial.map_add, twfPullback, twfPullback]

/-- The stationary pullback of a monomial. -/
private theorem twfPullback_C_mul_X_pow_twfMoebius (k j : ℕ) (c : ℤ[X]) :
    twfPullback (k + j) (C c * X ^ k) =
      C (c.comp (X ^ 2)) * (C (X ^ 2) * X + 1) ^ k * (C (X ^ 2) + X) ^ j := by
  have h : moebiusSubst (k + j) (C c * X ^ k) =
      C c * (C X * X + 1) ^ k * (C X + X) ^ j := by
    unfold moebiusSubst
    rw [Finset.sum_eq_single k]
    · rw [coeff_C_mul, coeff_X_pow_self, mul_one, Nat.add_sub_cancel_left]
    · intro i _ hi
      rw [coeff_C_mul, coeff_X_pow, ite_eq_right hi, mul_zero, C_0, zero_mul, zero_mul]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [twfPullback, h]
  simp [coe_compRingHom_apply]

/-- The identities for the value and the two first derivatives of a stationary pullback, without
assuming that the source vanishes. -/
private def TwfPullbackJet (n : ℕ) (m l J : ℂ) (f : ℤ[X][X]) : Prop :=
  evalIntHomTwfMoebius m l (twfPullback n f) =
      (l + m ^ 2) ^ n * evalIntHomTwfMoebius (m ^ 2) J f ∧
    (l + m ^ 2) * evalIntHomTwfMoebius m l (derivative (twfPullback n f)) =
      (l + m ^ 2) ^ n * ((m ^ 2 - J) * evalIntHomTwfMoebius (m ^ 2) J (derivative f) +
        (n : ℂ) * evalIntHomTwfMoebius (m ^ 2) J f) ∧
    (l + m ^ 2) * evalIntHomTwfMoebius m l (innerDerivative (twfPullback n f)) =
      2 * m * (l + m ^ 2) ^ n *
        ((l + m ^ 2) * evalIntHomTwfMoebius (m ^ 2) J (innerDerivative f) +
          (l - J) * evalIntHomTwfMoebius (m ^ 2) J (derivative f) +
          (n : ℂ) * evalIntHomTwfMoebius (m ^ 2) J f)

/-- The pullback identities are additive in the source. -/
private theorem twfPullbackJet_add {n : ℕ} {m l J : ℂ} {f g : ℤ[X][X]}
    (hf : TwfPullbackJet n m l J f) (hg : TwfPullbackJet n m l J g) :
    TwfPullbackJet n m l J (f + g) := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  obtain ⟨hg1, hg2, hg3⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · simp only [twfPullback_add_twfMoebius, map_add]
    linear_combination hf1 + hg1
  · simp only [twfPullback_add_twfMoebius, map_add]
    linear_combination hf2 + hg2
  · simp only [twfPullback_add_twfMoebius, innerDerivative_add, map_add]
    linear_combination hf3 + hg3

/-- The value of a product `a A^k B^j`. -/
private theorem map_mul_pow_pow_twfMoebius (E : ℤ[X][X] →+* ℂ) (a A B : ℤ[X][X]) (k j : ℕ) :
    E (a * A ^ k * B ^ j) = E a * E A ^ k * E B ^ j := by
  rw [map_mul, map_mul, map_pow, map_pow]

/-- The value of the derivative of a product `a A^k B^j`. -/
private theorem map_derivative_mul_pow_pow_twfMoebius (E : ℤ[X][X] →+* ℂ) (a A B : ℤ[X][X])
    (k j : ℕ) :
    E (derivative (a * A ^ k * B ^ j)) =
      E (derivative a) * E A ^ k * E B ^ j +
        E a * ((k : ℂ) * E A ^ (k - 1) * E (derivative A)) * E B ^ j +
        E a * E A ^ k * ((j : ℂ) * E B ^ (j - 1) * E (derivative B)) := by
  rw [derivative_mul, derivative_mul, derivative_pow, derivative_pow]
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

/-- The value of the inner derivative of a product `a A^k B^j`. -/
private theorem map_innerDerivative_mul_pow_pow_twfMoebius (E : ℤ[X][X] →+* ℂ)
    (a A B : ℤ[X][X]) (k j : ℕ) :
    E (innerDerivative (a * A ^ k * B ^ j)) =
      E (innerDerivative a) * E A ^ k * E B ^ j +
        E a * ((k : ℂ) * E A ^ (k - 1) * E (innerDerivative A)) * E B ^ j +
        E a * E A ^ k * ((j : ℂ) * E B ^ (j - 1) * E (innerDerivative B)) := by
  rw [innerDerivative_mul, innerDerivative_mul, innerDerivative_pow_twfMoebius,
    innerDerivative_pow_twfMoebius]
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

/-- The pullback identities for a monomial. -/
private theorem twfPullbackJet_C_mul_X_pow (k j : ℕ) (c : ℤ[X]) {m l J : ℂ}
    (hJ : J * (l + m ^ 2) = m ^ 2 * l + 1) :
    TwfPullbackJet (k + j) m l J (C c * X ^ k) := by
  have hA : evalIntHomTwfMoebius m l (C (X ^ 2) * X + 1) = J * (l + m ^ 2) := by
    rw [hJ]
    simp [evalIntHomTwfMoebius_C, evalIntHomTwfMoebius_X]
  have hB : evalIntHomTwfMoebius m l (C (X ^ 2) + X) = l + m ^ 2 := by
    simp [evalIntHomTwfMoebius_C, evalIntHomTwfMoebius_X, add_comm]
  have hc : evalIntHomTwfMoebius m l (C (c.comp (X ^ 2))) =
      (c.map (Int.castRingHom ℂ)).eval (m ^ 2) := by
    simp [evalIntHomTwfMoebius_C, Polynomial.map_comp, eval_comp]
  have hdc : evalIntHomTwfMoebius m l (derivative (C (c.comp (X ^ 2)))) = 0 := by
    rw [derivative_C, map_zero]
  have hic : evalIntHomTwfMoebius m l (innerDerivative (C (c.comp (X ^ 2)))) =
      2 * m * ((derivative c).map (Int.castRingHom ℂ)).eval (m ^ 2) := by
    rw [innerDerivative_C]
    simp [evalIntHomTwfMoebius_C, Polynomial.map_comp, eval_comp, derivative_comp]
  have hdA : evalIntHomTwfMoebius m l (derivative (C (X ^ 2) * X + 1 : ℤ[X][X])) = m ^ 2 := by
    rw [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_one]
    simp [evalIntHomTwfMoebius_C]
  have hdB : evalIntHomTwfMoebius m l (derivative (C (X ^ 2) + X : ℤ[X][X])) = 1 := by
    rw [derivative_add, derivative_C, derivative_X]
    simp
  have hiA : evalIntHomTwfMoebius m l (innerDerivative (C (X ^ 2) * X + 1 : ℤ[X][X])) =
      2 * m * l := by
    rw [innerDerivative_add, innerDerivative_mul, innerDerivative_C,
      innerDerivative_X_twfMoebius, innerDerivative_one_twfMoebius]
    simp [evalIntHomTwfMoebius_C, evalIntHomTwfMoebius_X]
  have hiB : evalIntHomTwfMoebius m l (innerDerivative (C (X ^ 2) + X : ℤ[X][X])) = 2 * m := by
    rw [innerDerivative_add, innerDerivative_C, innerDerivative_X_twfMoebius]
    simp [evalIntHomTwfMoebius_C]
  have hf : evalIntHomTwfMoebius (m ^ 2) J (C c * X ^ k) =
      (c.map (Int.castRingHom ℂ)).eval (m ^ 2) * J ^ k := by
    rw [map_mul, map_pow, evalIntHomTwfMoebius_C, evalIntHomTwfMoebius_X]
  have hdf : evalIntHomTwfMoebius (m ^ 2) J (derivative (C c * X ^ k)) =
      (c.map (Int.castRingHom ℂ)).eval (m ^ 2) * ((k : ℂ) * J ^ (k - 1)) := by
    have h := map_derivative_mul_pow_pow_twfMoebius (evalIntHomTwfMoebius (m ^ 2) J) (C c) X 1 k 0
    rw [pow_zero, mul_one] at h
    rw [h, derivative_C, derivative_X, derivative_one, map_zero, map_one,
      evalIntHomTwfMoebius_C, evalIntHomTwfMoebius_X]
    ring
  have hif : evalIntHomTwfMoebius (m ^ 2) J (innerDerivative (C c * X ^ k)) =
      ((derivative c).map (Int.castRingHom ℂ)).eval (m ^ 2) * J ^ k := by
    have h := map_innerDerivative_mul_pow_pow_twfMoebius (evalIntHomTwfMoebius (m ^ 2) J)
      (C c) X 1 k 0
    rw [pow_zero, mul_one] at h
    rw [h, innerDerivative_C, innerDerivative_X_twfMoebius, innerDerivative_one_twfMoebius,
      map_zero, map_one, evalIntHomTwfMoebius_C, evalIntHomTwfMoebius_X]
    ring
  rw [TwfPullbackJet, twfPullback_C_mul_X_pow_twfMoebius,
    map_derivative_mul_pow_pow_twfMoebius, map_innerDerivative_mul_pow_pow_twfMoebius,
    map_mul_pow_pow_twfMoebius, hf, hdf, hif, hA, hB, hc, hdc, hic, hdA, hdB, hiA, hiB]
  generalize (c.map (Int.castRingHom ℂ)).eval (m ^ 2) = cx
  generalize ((derivative c).map (Int.castRingHom ℂ)).eval (m ^ 2) = cx'
  generalize l + m ^ 2 = w
  refine ⟨?_, ?_, ?_⟩
  · ring
  · rcases k with _ | k <;> rcases j with _ | j <;>
      (try simp only [Nat.add_sub_cancel]) <;> push_cast <;> ring
  · rcases k with _ | k <;> rcases j with _ | j <;>
      (try simp only [Nat.add_sub_cancel]) <;> push_cast <;> ring

/-- The pullback identities for a polynomial of degree at most `n`. -/
private theorem twfPullbackJet_of_natDegree_le (n : ℕ) (f : ℤ[X][X]) (hf : f.natDegree ≤ n)
    {m l J : ℂ} (hJ : J * (l + m ^ 2) = m ^ 2 * l + 1) : TwfPullbackJet n m l J f := by
  have hsum : ∀ s : Finset ℕ, (∀ i ∈ s, i ≤ n) →
      TwfPullbackJet n m l J (∑ i ∈ s, C (f.coeff i) * X ^ i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp [TwfPullbackJet, twfPullback, moebiusSubst, innerDerivative]
    | insert i s hi ih =>
      intro hs
      rw [Finset.sum_insert hi]
      refine twfPullbackJet_add ?_ (ih fun i' hi' ↦ hs i' (Finset.mem_insert_of_mem hi'))
      have hin : i ≤ n := hs i (Finset.mem_insert_self i s)
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hin
      exact twfPullbackJet_C_mul_X_pow i j _ hJ
  have h := hsum (Finset.range (n + 1)) fun i hi ↦ Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rwa [← f.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hf)] at h

/-- The value of a stationary pullback. -/
theorem evalIntPoint_twfPullback (n : ℕ) (f : ℤ[X][X]) (hf : f.natDegree ≤ n) {m l J : ℂ}
    (hJ : J * (l + m ^ 2) = m ^ 2 * l + 1) :
    evalIntPoint (twfPullback n f) m l = (l + m ^ 2) ^ n * evalIntPoint f (m ^ 2) J :=
  (twfPullbackJet_of_natDegree_le n f hf hJ).1

/-- The `L`-derivative of a stationary pullback at a zero of its source. -/
theorem evalIntPoint_derivative_twfPullback (n : ℕ) (f : ℤ[X][X]) (hf : f.natDegree ≤ n)
    {m l J : ℂ} (hJ : J * (l + m ^ 2) = m ^ 2 * l + 1)
    (h0 : evalIntPoint f (m ^ 2) J = 0) :
    (l + m ^ 2) ^ 2 * evalIntPoint (derivative (twfPullback n f)) m l =
      (l + m ^ 2) ^ n * ((m ^ 2) ^ 2 - 1) * evalIntPoint (derivative f) (m ^ 2) J := by
  have h2 := (twfPullbackJet_of_natDegree_le n f hf hJ).2.1
  simp only [← evalIntPoint_eq_twfMoebius] at h2
  rw [h0, mul_zero, add_zero] at h2
  linear_combination (l + m ^ 2) * h2 -
    (l + m ^ 2) ^ n * evalIntPoint (derivative f) (m ^ 2) J * hJ

/-- The `M`-derivative of a stationary pullback at a zero of its source. -/
theorem evalIntPoint_coeffDerivative_twfPullback (n : ℕ) (f : ℤ[X][X]) (hf : f.natDegree ≤ n)
    {m l J : ℂ} (hJ : J * (l + m ^ 2) = m ^ 2 * l + 1)
    (h0 : evalIntPoint f (m ^ 2) J = 0) :
    (l + m ^ 2) ^ 2 * evalIntPoint (coeffDerivative (twfPullback n f)) m l =
      2 * m * (l + m ^ 2) ^ n *
        ((l + m ^ 2) ^ 2 * evalIntPoint (coeffDerivative f) (m ^ 2) J +
          (l ^ 2 - 1) * evalIntPoint (derivative f) (m ^ 2) J) := by
  have h3 := (twfPullbackJet_of_natDegree_le n f hf hJ).2.2
  simp only [← evalIntPoint_eq_twfMoebius, ← coeffDerivative_eq_innerDerivative] at h3
  rw [h0, mul_zero, add_zero] at h3
  linear_combination (l + m ^ 2) * h3 -
    2 * m * (l + m ^ 2) ^ n * evalIntPoint (derivative f) (m ^ 2) J * hJ

/-- The Jacobian of two stationary pullbacks at a common zero of their sources. -/
theorem twfPullback_jacobian (n n' : ℕ) (f g : ℤ[X][X]) (hf : f.natDegree ≤ n)
    (hg : g.natDegree ≤ n') {m l J : ℂ} (hJ : J * (l + m ^ 2) = m ^ 2 * l + 1)
    (hf0 : evalIntPoint f (m ^ 2) J = 0) (hg0 : evalIntPoint g (m ^ 2) J = 0) :
    (l + m ^ 2) ^ 2 *
        (evalIntPoint (derivative (twfPullback n f)) m l *
            evalIntPoint (coeffDerivative (twfPullback n' g)) m l -
          evalIntPoint (coeffDerivative (twfPullback n f)) m l *
            evalIntPoint (derivative (twfPullback n' g)) m l) =
      2 * m * (l + m ^ 2) ^ (n + n') * ((m ^ 2) ^ 2 - 1) *
        (evalIntPoint (derivative f) (m ^ 2) J * evalIntPoint (coeffDerivative g) (m ^ 2) J -
          evalIntPoint (coeffDerivative f) (m ^ 2) J * evalIntPoint (derivative g) (m ^ 2) J) := by
  obtain ⟨-, hf2, hf3⟩ := twfPullbackJet_of_natDegree_le n f hf hJ
  obtain ⟨-, hg2, hg3⟩ := twfPullbackJet_of_natDegree_le n' g hg hJ
  simp only [← evalIntPoint_eq_twfMoebius, ← coeffDerivative_eq_innerDerivative] at hf2 hf3 hg2 hg3
  rw [hf0, mul_zero, add_zero] at hf2 hf3
  rw [hg0, mul_zero, add_zero] at hg2 hg3
  linear_combination
    (l + m ^ 2) * evalIntPoint (coeffDerivative (twfPullback n' g)) m l * hf2 +
      (l + m ^ 2) ^ n * ((m ^ 2 - J) * evalIntPoint (derivative f) (m ^ 2) J) * hg3 -
      (l + m ^ 2) * evalIntPoint (derivative (twfPullback n' g)) m l * hf3 -
      2 * m * (l + m ^ 2) ^ n * ((l + m ^ 2) * evalIntPoint (coeffDerivative f) (m ^ 2) J +
        (l - J) * evalIntPoint (derivative f) (m ^ 2) J) * hg2 -
      2 * m * (l + m ^ 2) ^ (n + n') *
        (evalIntPoint (derivative f) (m ^ 2) J * evalIntPoint (coeffDerivative g) (m ^ 2) J -
          evalIntPoint (coeffDerivative f) (m ^ 2) J * evalIntPoint (derivative g) (m ^ 2) J) * hJ

end AJConjecture
