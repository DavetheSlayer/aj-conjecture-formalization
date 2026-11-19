import Mathlib
import AJPaper.Ideal.PpIEmbed
import AJPaper.Ideal.PpIShift

/-!
# Clearing negative exponents (Unit PpI, node `PpI_Clear`)

`ppi_exists_recOp_shift`: every element `P` of the quantum torus over `ℤ[t^{±1}]` has a left
multiple `t^c M^a L^b · P` that is a polynomial operator of the library:
`ppiOfRecOp Q = ppiShift a b c P` for some `Q ∈ ℤ[t][M][L]`.

Route: take `a ≥ -k` and `b ≥ -l` for all `(k, l)` in the (finite) support of `P`, and `c` such
that `t^{c + 2kb} c_{k,l}(t)` has only non-negative exponents for all `(k, l)` in the support
(`LaurentPolynomial.exists_T_pow` gives, for each coefficient, a power of `t` making it the
image of a polynomial; take the maximum over the support). Then
`Q = ∑_{(k,l)} monomial (l + b) (monomial (k + a) q_{k,l})` with
`toLaurent q_{k,l} = t^{c + 2kb} c_{k,l}`. Alternatively: induction on `P`
(`Finsupp.induction`) after showing that the set of `P` with the property is stable under sums
(raise the three exponents to a common value: a further shift of a polynomial operator is a
polynomial operator).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `ppiOfRecOp` is additive. -/
private theorem ppiOfRecOp_add_Clear (Q₁ Q₂ : RecOp) :
    ppiOfRecOp (Q₁ + Q₂) = ppiOfRecOp Q₁ + ppiOfRecOp Q₂ := by
  unfold ppiOfRecOp
  refine Polynomial.sum_add_index _ _ _ (fun i ↦ by simp) fun i D₁ D₂ ↦ ?_
  exact Polynomial.sum_add_index _ _ _ (fun j ↦ by simp) fun j c₁ c₂ ↦ by
    rw [map_add, Finsupp.single_add]

/-- `ppiOfRecOp` commutes with finite sums. -/
private theorem ppiOfRecOp_finset_sum_Clear {ι : Type} (s : Finset ι) (g : ι → RecOp) :
    ppiOfRecOp (∑ x ∈ s, g x) = ∑ x ∈ s, ppiOfRecOp (g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ppiOfRecOp]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ppiOfRecOp_add_Clear, ih]

/-- `ppiOfRecOp` of a monomial operator. -/
private theorem ppiOfRecOp_monomial_Clear (i j : ℕ) (q : ℤ[X]) :
    ppiOfRecOp (Polynomial.monomial i (Polynomial.monomial j q)) =
      Finsupp.single ((j : ℤ), (i : ℤ)) (Polynomial.toLaurent q) := by
  unfold ppiOfRecOp
  rw [Polynomial.sum_monomial_index _ _ (by simp), Polynomial.sum_monomial_index _ _ (by simp)]

/-- Every Laurent polynomial becomes a polynomial after multiplication by a large power
of `t`. -/
private theorem exists_toLaurent_eq_T_mul_Clear (x : LaurentPolynomial ℤ) :
    ∃ n : ℕ, ∀ m : ℤ, (n : ℤ) ≤ m → ∃ q : ℤ[X],
      Polynomial.toLaurent q = LaurentPolynomial.T m * x := by
  obtain ⟨n, q₀, hq₀⟩ := x.exists_T_pow
  refine ⟨n, fun m hm ↦ ⟨Polynomial.X ^ (m - n).toNat * q₀, ?_⟩⟩
  have hmn : m = ((m - n).toNat : ℤ) + n := by omega
  rw [map_mul, Polynomial.toLaurent_X_pow, hq₀]
  conv_rhs => rw [hmn, LaurentPolynomial.T_add]
  ring

/-- Every element of the quantum torus over `ℤ[t, t⁻¹]` has a left multiple by a monomial
`t^c M^a L^b` that is a polynomial operator. -/
theorem ppi_exists_recOp_shift (P : PpiOp ℤ) :
    ∃ (a b c : ℕ) (Q : RecOp), ppiOfRecOp Q = ppiShift a b c P := by
  choose N hN using fun kl : ℤ × ℤ ↦ exists_toLaurent_eq_T_mul_Clear (P kl)
  let a : ℕ := P.support.sup fun kl ↦ (-kl.1).toNat
  let b : ℕ := P.support.sup fun kl ↦ (-kl.2).toNat
  let c : ℕ := P.support.sup fun kl ↦ ((N kl : ℤ) - 2 * kl.1 * b).toNat
  have ha : ∀ kl ∈ P.support, (((kl.1 + a).toNat : ℕ) : ℤ) = kl.1 + a := fun kl hkl ↦ by
    have := Finset.le_sup (f := fun kl : ℤ × ℤ ↦ (-kl.1).toNat) hkl
    change (-kl.1).toNat ≤ a at this
    omega
  have hb : ∀ kl ∈ P.support, (((kl.2 + b).toNat : ℕ) : ℤ) = kl.2 + b := fun kl hkl ↦ by
    have := Finset.le_sup (f := fun kl : ℤ × ℤ ↦ (-kl.2).toNat) hkl
    change (-kl.2).toNat ≤ b at this
    omega
  have hc : ∀ kl ∈ P.support, (N kl : ℤ) ≤ (c : ℤ) + 2 * kl.1 * b := fun kl hkl ↦ by
    have := Finset.le_sup (f := fun kl : ℤ × ℤ ↦ ((N kl : ℤ) - 2 * kl.1 * b).toNat) hkl
    change ((N kl : ℤ) - 2 * kl.1 * b).toNat ≤ c at this
    omega
  have hq : ∀ kl : ℤ × ℤ, ∃ q : ℤ[X], kl ∈ P.support →
      Polynomial.toLaurent q = LaurentPolynomial.T ((c : ℤ) + 2 * kl.1 * b) * P kl := fun kl ↦ by
    by_cases hkl : kl ∈ P.support
    · obtain ⟨q, hq⟩ := hN kl _ (hc kl hkl)
      exact ⟨q, fun _ ↦ hq⟩
    · exact ⟨0, fun h ↦ absurd h hkl⟩
  choose q hq using hq
  refine ⟨a, b, c, ∑ kl ∈ P.support, Polynomial.monomial (kl.2 + b).toNat
    (Polynomial.monomial (kl.1 + a).toNat (q kl)), ?_⟩
  rw [ppiOfRecOp_finset_sum_Clear]
  unfold ppiShift Finsupp.sum
  refine Finset.sum_congr rfl fun kl hkl ↦ ?_
  rw [ppiOfRecOp_monomial_Clear, ha kl hkl, hb kl hkl, hq kl hkl]

end AJConjecture
