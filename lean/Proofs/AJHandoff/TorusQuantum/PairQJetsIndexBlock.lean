import Mathlib
import AJConjecture.QAlgSymbolNodeDerivatives
import AJHandoff.TorusQuantum.PairQJetsIndexReflect

/-!
# T-JETS: residual blocks in the backward variable

A block `b ∈ ℤ[M][L]` of degree `n` in `L` becomes, in `u = L⁻¹`, its reversal
`b̂ = u^n b(z, 1/u)` with complex coefficients (`pairQJetBlock`). At `u = l⁻¹`:
`b̂ · lⁿ = b`, `(∂_z b̂) · lⁿ = ∂_M b`, `(∂_u b̂) · lⁿ = l (n b - l ∂_L b)` (right-hand sides at
`(M, L) = (m, l)`). A factorization `κ₁ P₀ = κ₂ ∏ b_i` of the forward symbol reverses to
`κ₁ u^d P₀(1/u) = κ₂ ∏ b̂_i` (`pairQJet_sym`), with `d = deg P₀`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The reversal `u^n b(z, 1/u)` (`n = deg_L b`) of `b ∈ ℤ[M][L]`, with complex coefficients. -/
def pairQJetBlock (b : ℤ[X][X]) : ℂ[X][X] :=
  (b.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).reverse

/-- Evaluation of `ℤ[M][L]` at a complex point, as a ring homomorphism. -/
def pairQJetEvalHom (m l : ℂ) : ℤ[X][X] →+* ℂ :=
  (Polynomial.eval₂RingHom (Polynomial.evalRingHom m) l).comp
    (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℂ)))

theorem evalIntPoint_eq_pairQJetEvalHom (p : ℤ[X][X]) (m l : ℂ) :
    evalIntPoint p m l = pairQJetEvalHom m l p :=
  rfl

theorem pairQJetEvalHom_C (m l : ℂ) (κ : ℤ[X]) :
    pairQJetEvalHom m l (C κ) = (κ.map (Int.castRingHom ℂ)).eval m := by
  simp [pairQJetEvalHom]

/-- The complexification of `ℤ[M][L]` is injective. -/
theorem mapRingHom_intCast_injective_pairQ :
    Function.Injective (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) :
      ℤ[X][X] → ℂ[X][X]) :=
  Polynomial.map_injective _ (Polynomial.map_injective _ Int.cast_injective)

theorem natDegree_map_intCast_pairQ (b : ℤ[X][X]) :
    (b.map (Polynomial.mapRingHom (Int.castRingHom ℂ))).natDegree = b.natDegree :=
  natDegree_map_eq_of_injective (Polynomial.map_injective _ Int.cast_injective) b

theorem pairQJetBlock_eq_reflect (b : ℤ[X][X]) :
    pairQJetBlock b = reflect b.natDegree (b.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
  rw [pairQJetBlock, reverse, natDegree_map_intCast_pairQ]

/-- The value of a reversed block at `u = l⁻¹`. -/
theorem evalPoint_pairQJetBlock (b : ℤ[X][X]) (m : ℂ) {l : ℂ} (hl : l ≠ 0) :
    evalPoint (pairQJetBlock b) (m, l⁻¹) * l ^ b.natDegree = evalIntPoint b m l := by
  rw [pairQJetBlock_eq_reflect]
  exact evalPoint_reflect_inv_pairQ (natDegree_map_intCast_pairQ b).le m hl

/-- The `u`-derivative of a reversed block at `u = l⁻¹`. -/
theorem evalPoint_derivative_pairQJetBlock (b : ℤ[X][X]) (m : ℂ) {l : ℂ} (hl : l ≠ 0) :
    evalPoint (derivative (pairQJetBlock b)) (m, l⁻¹) * l ^ b.natDegree =
      l * (b.natDegree * evalIntPoint b m l - l * evalIntPoint (derivative b) m l) := by
  rw [pairQJetBlock_eq_reflect, evalPoint_derivative_reflect_inv_pairQ
    (natDegree_map_intCast_pairQ b).le m hl, evalIntPoint, evalIntPoint, derivative_map]

/-- The `z`-derivative of a reversed block at `u = l⁻¹`. -/
theorem evalPoint_innerDerivative_pairQJetBlock (b : ℤ[X][X]) (m : ℂ) {l : ℂ} (hl : l ≠ 0) :
    evalPoint (innerDerivative (pairQJetBlock b)) (m, l⁻¹) * l ^ b.natDegree =
      evalIntPoint (coeffDerivative b) m l := by
  rw [pairQJetBlock_eq_reflect, evalPoint_innerDerivative_reflect_inv_pairQ
    (natDegree_map_intCast_pairQ b).le m hl, innerDerivative_map, evalIntPoint,
    coeffDerivative_eq_innerDerivative]

/-- Reversal is multiplicative over a domain. -/
theorem reverse_prod_pairQ {R ι : Type*} [CommSemiring R] [NoZeroDivisors R] (s : Finset ι)
    (f : ι → R[X]) : (∏ i ∈ s, f i).reverse = ∏ i ∈ s, (f i).reverse := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using reverse_C (1 : R)
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, reverse_mul_of_domain, ih]

/-- The symbol factorization in the backward variable. -/
theorem pairQJet_sym {P : RecOp} {ι : Type*} [Fintype ι] {b : ι → ℤ[X][X]} {κ₁ κ₂ : ℤ[X]}
    (hsym : C κ₁ * specialize P = C κ₂ * ∏ i, b i)
    (hdeg : (specialize P).natDegree = P.natDegree) :
    C (κ₁.map (Int.castRingHom ℂ)) * opJet0 (pairQJetRow P) =
      C (κ₂.map (Int.castRingHom ℂ)) * ∏ i, pairQJetBlock (b i) := by
  have h := congrArg (Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) hsym
  rw [Polynomial.map_mul, Polynomial.map_mul, map_C, map_C, Polynomial.map_prod] at h
  have h' := congrArg reverse h
  rw [reverse_mul_of_domain, reverse_mul_of_domain, reverse_C, reverse_C, reverse_prod_pairQ] at h'
  rw [opJet0_pairQJetRow, ← hdeg, pairQJetSymbol, ← natDegree_map_intCast_pairQ, ← reverse]
  exact h'

end AJConjecture
