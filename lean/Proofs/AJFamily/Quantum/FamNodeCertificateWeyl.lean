import Mathlib
import AJConjecture.QAlgSymbolNodeDerivatives
import AJFamily.Quantum.FamNodeCertificate
import AJFamily.Quantum.FamSymbol

/-!
# The Weyl symbol from a node certificate

`evalIntPoint_weylSymbol_famTransferOp_of_certificate`: at a common zero of `G` and `D`, where
`G D T = (L - 1) E B_m`, the Weyl subprincipal symbol of `famTransferOp m` vanishes once the
first-order data of the node satisfy one numerical identity, the certificate identity.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The final elimination: from the second derivatives of the symbol, the first jet and the
numerical identity, the Weyl symbol vanishes. -/
private theorem weyl_eq_zero_of_certificate_numbers_famNodeCertificateWeyl
    {γ K₁ K₂ d T P₁ P₂ E c l m h₁ g₁ d₁ g₂ d₂ : ℂ} (hγ : γ ≠ 0) (hK : K₁ ≠ 0)
    (h2 : K₁ * P₂ = 2 * (d * K₂) * (g₁ * d₁) * T)
    (h3 : K₁ * E = d * K₂ * (l * m) * (g₁ * d₂ + g₂ * d₁) * T)
    (hjet : γ * (P₁ + c * l ^ 2 * P₂) = d * h₁)
    (hnum : h₁ * K₁ = γ * K₂ * T * (2 * c * l ^ 2 * (g₁ * d₁) - l * m * (g₁ * d₂ + g₂ * d₁))) :
    P₁ + E = 0 := by
  have h : γ * K₁ * (P₁ + E) = 0 := by
    linear_combination K₁ * hjet - γ * c * l ^ 2 * h2 + γ * h3 + d * hnum
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hγ hK)

/-- The Weyl subprincipal symbol of the family transfer operator vanishes at a node of `G` and
`D` when the certificate numbers satisfy the final numerical identity. -/
theorem evalIntPoint_weylSymbol_famTransferOp_of_certificate (m : ℕ) (hm : 1 ≤ m)
    {G D T : ℤ[X][X]} (hGDT : G * D * T = (X - 1) * extraFactor * twistPoly m)
    {m₀ l₀ J₀ γ a b c h₁ : ℂ} (hγ : γ ≠ 0)
    (hκ : (m₀ ^ 2 - 1) ^ (2 * m + 3) * ((m₀ ^ 2) ^ 2 - 1) ^ (2 * m + 3) ≠ 0)
    (hG : evalIntPoint G m₀ l₀ = 0) (hD : evalIntPoint D m₀ l₀ = 0)
    (hbasis : ∀ i : Fin (2 * m + 4),
      (famBasisPoly m dualQ i).evalEval (famDualX m m₀) (TrivSqZeroExt.inl J₀) =
        TrivSqZeroExt.inl (γ * l₀ ^ (2 * m + 3 - (i : ℕ))) *
          (1 + TrivSqZeroExt.inl (a + b * ((i : ℕ) : ℂ) + c * ((i : ℕ) : ℂ) ^ 2) *
            DualNumber.eps))
    (htarget : (famTarget m dualQ).evalEval (famDualX m m₀) (TrivSqZeroExt.inl J₀) =
      TrivSqZeroExt.inl h₁ * DualNumber.eps)
    (hnum : h₁ * ((m₀ ^ 2 - 1) ^ (2 * m + 3) * ((m₀ ^ 2) ^ 2 - 1) ^ (2 * m + 3)) =
      γ * ((m₀ ^ 2 + 1) ^ 2 * (m₀ ^ 2 - 1)) * evalIntPoint T m₀ l₀ *
        (2 * c * l₀ ^ 2 *
            (evalIntPoint (derivative G) m₀ l₀ * evalIntPoint (derivative D) m₀ l₀) -
          l₀ * m₀ *
            (evalIntPoint (derivative G) m₀ l₀ * evalIntPoint (coeffDerivative D) m₀ l₀ +
              evalIntPoint (coeffDerivative G) m₀ l₀ * evalIntPoint (derivative D) m₀ l₀))) :
    evalIntPoint (weylSymbol (famTransferOp m)) m₀ l₀ = 0 := by
  have hsym := specialize_famTransferOp_mul_eq m hm
  rw [← hGDT] at hsym
  have hK₁ : (((X ^ 2 - 1) ^ (2 * m + 3) * (X ^ 4 - 1) ^ (2 * m + 3) : ℤ[X]).map
      (Int.castRingHom ℂ)).eval m₀ =
      (m₀ ^ 2 - 1) ^ (2 * m + 3) * ((m₀ ^ 2) ^ 2 - 1) ^ (2 * m + 3) := by
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X,
      Polynomial.map_one, eval_mul, eval_pow, eval_sub, eval_X, eval_one]
    rw [← pow_mul]
  have hK₂ : (((famDet m (1 : ℤ)).comp (X ^ 2) * ((X ^ 2 + 1) ^ 2 * (X ^ 2 - 1)) : ℤ[X]).map
      (Int.castRingHom ℂ)).eval m₀ =
      ((famDet m (1 : ℤ)).map (Int.castRingHom ℂ)).eval (m₀ ^ 2) *
        ((m₀ ^ 2 + 1) ^ 2 * (m₀ ^ 2 - 1)) := by
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
      map_X, Polynomial.map_one, Polynomial.map_comp, eval_mul, eval_pow, eval_sub, eval_add,
      eval_X, eval_one, eval_comp]
  obtain ⟨h0, h1, h2, h3⟩ := evalIntPoint_derivatives_of_symbol_node hsym
    (by rw [hK₁]; exact hκ) hG hD
  rw [hK₁, hK₂] at h2 h3
  rw [weylSymbol, evalIntPoint_add]
  exact weyl_eq_zero_of_certificate_numbers_famNodeCertificateWeyl hγ hκ h2 h3
    (evalIntPoint_specializeJet_famTransferOp_of_jets m hm hbasis htarget h0 h1) hnum

end AJConjecture
