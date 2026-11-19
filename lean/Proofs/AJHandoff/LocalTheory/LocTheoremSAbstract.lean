import Mathlib
import AJConjecture.QAlgOreMulAssoc
import AJConjecture.QAlgOrePseudoDivision
import AJHandoff.LocalTheory.LocPseudoField

/-!
# Theorem S for difference rings

Let `K` be a field with an endomorphism `τ`, and `(E, L)` a commutative difference ring containing
`K` through `ev : K → E` with `L ∘ ev = ev ∘ τ`. Operators `P = ∑ a_i u^i ∈ K[u; τ]` act by
`P · f = ∑ ev(a_i) L^i f`; this is a left module action (`diffAct_oreMul`). Let `W ⊆ E` be an
additive subgroup stable under `L` and under multiplication by `ev(K)` (the "rational"
elements: for sequences, the image of `K`; or `W = 0`).

**Theorem S.** If `P` is irreducible in `K[u; τ]`, `F ∉ W` and `P · F ∈ W` (forcing in `W`,
including `0`), then every `G` with `G · F = 0` is a left multiple `H ⋆ P`.

Proof. The operators `Q` with `Q · F ∈ W` form a left ideal containing `P`. A nonzero element
`Q₀` of minimal degree right-divides each member (right division in `K[u; τ]`, the library's
`exists_C_mul_eq_oreMul_add` over a field). So `P = S ⋆ Q₀`; by irreducibility `Q₀` has degree `0`
(then `F ∈ W`, excluded) or `S` has degree `0`, i.e. `Q₀` is `P` up to a scalar. Since `G · F = 0`,
`G` is in the ideal, so `Q₀` right-divides `G`. This is the source's greatest-common-right-divisor
argument; the source takes `W = K` (inhomogeneous forcing), the toy application `W = 0`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The action `P · f = ∑ ev(a_i) L^i f` of an operator on a difference ring. -/
def diffAct {K E : Type*} [CommRing K] [CommRing E] (ev : K →+* E) (L : E →+* E) (P : K[X])
    (f : E) : E :=
  P.sum fun i a ↦ ev a * L^[i] f

/-- The action is additive in the operator. -/
theorem diffAct_add_left {K E : Type*} [CommRing K] [CommRing E] (ev : K →+* E) (L : E →+* E)
    (P Q : K[X]) (f : E) : diffAct ev L (P + Q) f = diffAct ev L P f + diffAct ev L Q f := by
  unfold diffAct
  exact Polynomial.sum_add_index _ _ _ (fun _ ↦ by rw [map_zero, zero_mul])
    fun _ _ _ ↦ by rw [map_add, add_mul]

/-- The action of a monomial. -/
theorem diffAct_monomial {K E : Type*} [CommRing K] [CommRing E] (ev : K →+* E) (L : E →+* E)
    (n : ℕ) (a : K) (f : E) : diffAct ev L (monomial n a) f = ev a * L^[n] f := by
  unfold diffAct
  exact Polynomial.sum_monomial_index _ _ (by rw [map_zero, zero_mul])

/-- The action of a constant operator. -/
private theorem diffAct_C {K E : Type*} [CommRing K] [CommRing E] (ev : K →+* E) (L : E →+* E)
    (a : K) (f : E) : diffAct ev L (C a) f = ev a * f := by
  rw [← Polynomial.monomial_zero_left, diffAct_monomial, Function.iterate_zero, id]

/-- The action is additive in the sequence. -/
private theorem diffAct_add_right {K E : Type*} [CommRing K] [CommRing E] (ev : K →+* E) (L : E →+* E)
    (P : K[X]) (f g : E) : diffAct ev L P (f + g) = diffAct ev L P f + diffAct ev L P g := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [diffAct_add_left, diffAct_add_left, diffAct_add_left, hp, hq]; ring
  | monomial n a => rw [diffAct_monomial, diffAct_monomial, diffAct_monomial,
      iterate_map_add, mul_add]

/-- Iterates of `L` on the image of `ev`. -/
private theorem iterate_diffShift_ev {K E : Type*} [CommRing K] [CommRing E] (τ : K →+* K)
    (ev : K →+* E) (L : E →+* E) (hL : ∀ a, L (ev a) = ev (τ a)) (i : ℕ) (a : K) :
    L^[i] (ev a) = ev (τ^[i] a) := by
  induction i generalizing a with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hL, ih]

theorem diffAct_oreMul {K E : Type*} [CommRing K] [CommRing E] (τ : K →+* K) (ev : K →+* E)
    (L : E →+* E) (hL : ∀ a, L (ev a) = ev (τ a)) (P Q : K[X]) (f : E) :
    diffAct ev L (oreMul τ P Q) f = diffAct ev L P (diffAct ev L Q f) := by
  induction P using Polynomial.induction_on' with
  | add p p' hp hp' => rw [oreMul_add_left, diffAct_add_left, diffAct_add_left, hp, hp']
  | monomial i a =>
    induction Q using Polynomial.induction_on' with
    | add q q' hq hq' => rw [oreMul_add_right, diffAct_add_left, diffAct_add_left, hq, hq',
        diffAct_add_right]
    | monomial k b =>
      rw [oreMul_monomial_monomial, diffAct_monomial, diffAct_monomial, diffAct_monomial,
        iterate_map_mul, iterate_diffShift_ev τ ev L hL, map_mul, ← Function.iterate_add_apply]
      ring

/-- An operator maps an `L`- and `ev(K)`-stable additive subgroup into itself. -/
private theorem diffAct_mem_of_mem {K E : Type*} [CommRing K] [CommRing E] (ev : K →+* E)
    (L : E →+* E) (W : AddSubgroup E) (hWK : ∀ (a : K) (w : E), w ∈ W → ev a * w ∈ W)
    (hWL : ∀ w ∈ W, L w ∈ W) (S : K[X]) {w : E} (hw : w ∈ W) : diffAct ev L S w ∈ W := by
  induction S using Polynomial.induction_on' with
  | add p q hp hq => rw [diffAct_add_left]; exact W.add_mem hp hq
  | monomial n a =>
    rw [diffAct_monomial]
    refine hWK a _ ?_
    induction n with
    | zero => exact hw
    | succ n ih => rw [Function.iterate_succ_apply']; exact hWL _ ih

/-- In the left ideal `{Q : Q · F ∈ W}`, a nonzero element of minimal degree right-divides every
member. -/
private theorem exists_eq_oreMul_of_diffAct_mem_of_minimal {K E : Type*} [Field K] [CommRing E]
    (τ : K →+* K) (ev : K →+* E) (L : E →+* E) (hL : ∀ a, L (ev a) = ev (τ a))
    (W : AddSubgroup E) (hWK : ∀ (a : K) (w : E), w ∈ W → ev a * w ∈ W)
    (hWL : ∀ w ∈ W, L w ∈ W) {F : E} {Q₀ : K[X]} (hQ₀ : Q₀ ≠ 0)
    (hQ₀W : diffAct ev L Q₀ F ∈ W)
    (hmin : ∀ R : K[X], R ≠ 0 → diffAct ev L R F ∈ W → Q₀.natDegree ≤ R.natDegree)
    {Q : K[X]} (hQ : diffAct ev L Q F ∈ W) : ∃ T : K[X], Q = oreMul τ T Q₀ := by
  obtain ⟨β, hβ, S, R, hdiv, hdeg⟩ := exists_C_mul_eq_oreMul_add τ.injective Q hQ₀
  have hsum := congrArg (fun X ↦ diffAct ev L X F) hdiv
  simp only [diffAct_add_left, ← oreMul_C_left τ, diffAct_oreMul τ ev L hL, diffAct_C] at hsum
  have hRW : diffAct ev L R F ∈ W := by
    have h1 : ev β * diffAct ev L Q F ∈ W := hWK β _ hQ
    have h2 := diffAct_mem_of_mem ev L W hWK hWL S hQ₀W
    have : diffAct ev L R F = ev β * diffAct ev L Q F - diffAct ev L S (diffAct ev L Q₀ F) := by
      rw [hsum]; ring
    rw [this]
    exact W.sub_mem h1 h2
  have hR : R = 0 := by
    by_contra hR
    have := hmin R hR hRW
    have := Polynomial.natDegree_lt_natDegree hR hdeg
    omega
  refine ⟨C β⁻¹ * S, ?_⟩
  rw [hR, add_zero] at hdiv
  rw [← C_mul_oreMul, ← hdiv, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hβ,
    Polynomial.C_1, one_mul]

/-- **Theorem S** (abstract form). -/
theorem exists_eq_oreMul_of_diffAct_eq_zero {K E : Type*} [Field K] [CommRing E] (τ : K →+* K)
    (ev : K →+* E) (L : E →+* E) (hL : ∀ a, L (ev a) = ev (τ a)) (W : AddSubgroup E)
    (hWK : ∀ (a : K) (w : E), w ∈ W → ev a * w ∈ W) (hWL : ∀ w ∈ W, L w ∈ W) {P : K[X]}
    (hP : OreIrreducible τ P) {F : E} (hF : F ∉ W) (hPF : diffAct ev L P F ∈ W) {G : K[X]}
    (hG : diffAct ev L G F = 0) : ∃ H : K[X], G = oreMul τ H P := by
  classical
  have hP0 : P ≠ 0 := fun h ↦ by have := hP.1; rw [h, natDegree_zero] at this; omega
  have hex : ∃ n : ℕ, ∃ Q : K[X], Q ≠ 0 ∧ diffAct ev L Q F ∈ W ∧ Q.natDegree = n :=
    ⟨_, P, hP0, hPF, rfl⟩
  obtain ⟨Q₀, hQ₀, hQ₀W, hQ₀n⟩ := Nat.find_spec hex
  have hmin : ∀ R : K[X], R ≠ 0 → diffAct ev L R F ∈ W → Q₀.natDegree ≤ R.natDegree :=
    fun R hR hRW ↦ hQ₀n ▸ Nat.find_min' hex ⟨R, hR, hRW, rfl⟩
  have hdivides := fun {Q : K[X]} (hQ : diffAct ev L Q F ∈ W) ↦
    exists_eq_oreMul_of_diffAct_mem_of_minimal τ ev L hL W hWK hWL hQ₀ hQ₀W hmin hQ
  obtain ⟨S, hS⟩ := hdivides hPF
  obtain ⟨T, hT⟩ := hdivides (show diffAct ev L G F ∈ W by rw [hG]; exact W.zero_mem)
  rcases hP.2 S Q₀ hS.symm with h0 | h0
  · exfalso
    rw [Polynomial.eq_C_of_natDegree_eq_zero h0, diffAct_C] at hQ₀W
    have hc : Q₀.coeff 0 ≠ 0 := fun hc ↦ hQ₀ <| by
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero]
    apply hF
    have := hWK (Q₀.coeff 0)⁻¹ _ hQ₀W
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] at this
  · rw [Polynomial.eq_C_of_natDegree_eq_zero h0, oreMul_C_left] at hS
    have hs : S.coeff 0 ≠ 0 := fun hs ↦ hP0 <| by rw [hS, hs, map_zero, zero_mul]
    refine ⟨oreMul τ T (C (S.coeff 0)⁻¹), ?_⟩
    rw [oreMul_assoc, oreMul_C_left, hS, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hs,
      Polynomial.C_1, one_mul, hT]

end AJConjecture
