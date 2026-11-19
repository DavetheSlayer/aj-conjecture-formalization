import Mathlib
import AJConjecture.QAlgOreMulBasic

/-!
# The Ore product commutes with ring homomorphisms

If `f : A → B` intertwines the endomorphisms `σ` of `A` and `τ` of `B`, then mapping the
coefficients by `f` is multiplicative for the Ore products. Proof: bilinearity
(`oreMul_add_left`, `oreMul_add_right`) reduces to `oreMul_monomial_monomial`, where
`f (σ^[i] b) = τ^[i] (f b)` by induction on `i`.
-/

open Polynomial

namespace AJConjecture

/-- Mapping coefficients along a homomorphism that intertwines the twists is multiplicative for
the Ore products. -/
theorem map_oreMul {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) (σ : A →+* A)
    (τ : B →+* B) (hf : ∀ a, f (σ a) = τ (f a)) (P Q : A[X]) :
    (oreMul σ P Q).map f = oreMul τ (P.map f) (Q.map f) := by
  have hiter : ∀ (i : ℕ) (a : A), f (σ^[i] a) = τ^[i] (f a) := by
    intro i
    induction i with
    | zero => intro a; rfl
    | succ i ih =>
      intro a
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hf]
  induction P using Polynomial.induction_on' with
  | add p p' hp hp' =>
    rw [oreMul_add_left, Polynomial.map_add, Polynomial.map_add, oreMul_add_left, hp, hp']
  | monomial i a =>
    induction Q using Polynomial.induction_on' with
    | add q q' hq hq' =>
      rw [oreMul_add_right, Polynomial.map_add, Polynomial.map_add, oreMul_add_right, hq, hq']
    | monomial k b =>
      rw [oreMul_monomial_monomial, map_monomial, map_monomial, map_monomial,
        oreMul_monomial_monomial, map_mul, hiter]

end AJConjecture
