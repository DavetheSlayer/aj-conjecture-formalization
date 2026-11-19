import Mathlib
import AJTwist.Factor.TwFNegTargetJet
import AJTwist.Factor.TwFNegEbNode

/-!
# The crossing `E/C_b`: the certificate identity (TwF, unit F2, crux)

Source: revision 5, Section 5.4 (`operators.tex`), "The `E/C_b` crossing":
`Ṅ_(-b) = -s_b (56b² - 16b + 2)/(3 h_b³)`, `s_G = -4b/(4b - 1)`,
`s_H = -(24b³ - 8b² + 2b)/(10b² - 5b + 1)`,
`(D_u G)(D_u H) = -s_b 2(4b - 1)(10b² - 5b + 1)/(3b h_b² (8b² - 4b + 1))`, `ρ = 4b²/h_b`,
"The normalized jet is `κ = (s_G + s_H)/2`".

`twNeg_ebNode_cert`: at the `E/C_b` node (`x₀ = m₀²` a root of
`b(2b - 1) x² + (4b² - 2b + 1) x + b(2b - 1)`, `J₀ = twNegNodeJ b`, `w = -x₀`),

`h₁ (x₀² - 1) = 2 x₀ (1 - x₀J₀)(x₀ - J₀) ∂_x∂_J p`,   `h₁ = twNegTargetJet b x₀ J₀ (-x₀)`,
`p = twNegTarget b 1`.

This is the hypothesis `hcert` of `evalIntPoint_weylSymbol_twTransferOp_eq_zero`; in the paper's
notation it is `κ = (s_G + s_H)/2` (with `h₁ = -4 x₀^(b+1) Ṅ_(-b)`).

Route. Right side: `twNegTarget_one_derivatives_ebNode`, then `symbolTwistNeg_node_values` with
`w = -x₀` and `dblRootDeriv_mul_of_crit` (the zero condition is `-x₀ + b δ = 0`,
`δ = x₀² + x₀ + 1 - x₀J₀`, from `twNeg_ebNode_zeta`). Left side: unfold `twNegTargetJet`. Both
sides are `(-x₀)^(b-2)` times rational functions of `(b, x₀)` (`J₀` is rational in `b`); clear
the denominators `2b - 1`, `b`, `6` and close with `linear_combination (cofactor) * heb`.
Computed symbolically in `b` (scratch `node_closed_neg.py`): after substituting
`J₀ = (b x₀² + b x₀ + b - x₀)/(b x₀)` the difference of the two sides has denominator `3 b⁶ x₀³`
and numerator `2 x₀² · (polynomial of degree 8 in x₀, 7 in b) · (node quadratic)`; reducing all
node values modulo the node quadratic first (linear forms in `x₀`, as in the library's
`ebNode_lin_*`) gives smaller certificates. The cases `b = 1, 2`, where `w ^ (b - 2)`,
`w ^ (b - 3)` are truncated, are separate explicit computations.
Checked: the identity for `1 ≤ b ≤ 8` modulo a prime (scratch `check_weyl.py`), and all the
constants quoted above (scratch `check_paper5.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The first jet `twNegTargetJet b (-w) J w` with the powers `w ^ (b + j)` replaced by
`t * w ^ (j + 3)`, `-3 ≤ j ≤ 1`, and `b` by a complex parameter. -/
private def twNegEbJetT (β w J t : ℂ) : ℂ :=
  let x : ℂ := -w
  let d : ℂ := 2 * β + 2
  let z₁ : ℂ := -8 * d * x ^ 2 - 4 * d * (1 + x) - 4 * d * x +
    J * (-8 * d * x + 4 * (d + 1) + 4 * x * (1 + x) + 4 * d * x * (1 + x) + 4 * d * x ^ 2) -
    (8 + 4 * d) * x * J ^ 2
  let s₁ : ℂ := -(16 * d - 4) * x ^ 2
  let A₀ : ℂ := (1 - J) * (x - J) * (1 - x * J)
  let zJ : ℂ := -1 - x ^ 2 + 2 * x * J
  ((β + 1) ^ 2 * (t * w ^ 3) * z₁ - (β + 1) * β * (t * w ^ 2) * s₁ -
      4 * (β + 1) * (2 * (t * w ^ 4)) +
      4 * A₀ * ((β + 1) ^ 2 * ((β + 1) ^ 2 - 1) / 12 * (t * w ^ 2)) * zJ) +
    x * ((1 - J) * (β ^ 2 * (t * w ^ 2) * z₁ - β * (β - 1) * (t * w) * s₁) +
      4 * J * (2 * (t * w ^ 3)) - (4 * β + 8 * d) * (1 - J) * (2 * (t * w ^ 3)) +
      4 * A₀ * (-(β ^ 2 * (t * w ^ 2)) + β ^ 2 * (β ^ 2 - 1) / 12 * (t * w) * zJ * (1 - J))) -
    x ^ 2 * (J * ((β - 1) ^ 2 * (t * w) * z₁ - (β - 1) * (β - 2) * t * s₁) -
      (4 * β + 16 * d) * J * (2 * (t * w ^ 2)) +
      4 * A₀ * ((β - 1) ^ 2 * (t * w) + (β - 1) ^ 2 * ((β - 1) ^ 2 - 1) / 12 * t * zJ * J))

/-- The difference of the two sides of the certificate identity (times `6 w`), with the powers
`w ^ (b + j)` replaced by `t * w ^ (j + 3)`. -/
private def twNegEbCertDiff (β w J t : ℂ) : ℂ :=
  6 * w * twNegEbJetT β w J t * (w ^ 2 - 1) -
    2 * -w * ((1 - -w * J) * (-w - J)) * ((1 - J) *
      ((2 * -w * J - ((-w) ^ 2 + 1)) * (t * w ^ 2 * (6 * β * w * (2 * -w - J) +
          (β - 1) * (2 * β - 1) * (J ^ 2 - 2 * -w * J + 2 * -w + 1) * w -
          2 * (β - 1) * (β + 1) * (2 * -w))) +
        (J ^ 2 - 2 * -w * J + 2 * -w + 1 + 2) * (t * w ^ 2 * (6 * β * w * - -w +
          (β - 1) * (2 * β - 1) * (2 * -w * J - ((-w) ^ 2 + 1)) * w -
          2 * (β - 1) * (β + 1) * 0))))

/-- The homogenization of `twNegEbCertDiff` in `J = K / s` (degree `6`), expanded. -/
private def twNegEbCertHom (β w K s t : ℂ) : ℂ :=
  t * (
    4 * w ^ 4 * (2 * β ^ 3 * w ^ 4 - 2 * β ^ 3 - 49 * β ^ 2 * w ^ 4 + 150 * β ^ 2 * w ^ 3 +
      20 * β ^ 2 * w ^ 2 - 138 * β ^ 2 * w + 21 * β ^ 2 - 71 * β * w ^ 4 + 192 * β * w ^ 3 +
      27 * β * w ^ 2 - 198 * β * w + 35 * β - 26 * w ^ 4 + 66 * w ^ 3 + 10 * w ^ 2 - 66 * w +
      12) * (s ^ 6) +
    4 * w ^ 3 * (2 * β ^ 3 * w ^ 6 + 6 * β ^ 3 * w ^ 4 - 6 * β ^ 3 * w ^ 2 - 2 * β ^ 3 -
      β ^ 2 * w ^ 6 + 8 * β ^ 2 * w ^ 5 + 155 * β ^ 2 * w ^ 4 + 32 * β ^ 2 * w ^ 3 -
      187 * β ^ 2 * w ^ 2 + 12 * β ^ 2 * w - 3 * β ^ 2 + β * w ^ 6 + 42 * β * w ^ 5 +
      81 * β * w ^ 4 - 39 * β * w ^ 3 - 105 * β * w ^ 2 - 30 * β * w - β - 2 * w ^ 6 + 64 * w ^ 5 -
      80 * w ^ 4 - 20 * w ^ 3 + 70 * w ^ 2 - 36 * w) * (K * s ^ 5) +
    4 * w ^ 3 * (4 * β ^ 3 * w ^ 5 - 4 * β ^ 3 * w + 2 * β ^ 2 * w ^ 6 + 38 * β ^ 2 * w ^ 5 +
      82 * β ^ 2 * w ^ 4 - 64 * β ^ 2 * w ^ 3 - 2 * β ^ 2 * w ^ 2 - 42 * β ^ 2 * w + 6 * β ^ 2 -
      6 * β * w ^ 6 + 47 * β * w ^ 5 + 27 * β * w ^ 4 - 18 * β * w ^ 3 - 63 * β * w ^ 2 -
      35 * β * w + 4 * w ^ 6 - 44 * w ^ 5 + 41 * w ^ 4 + 4 * w ^ 3 - 19 * w ^ 2 +
      24 * w) * (K ^ 2 * s ^ 4) +
    -4 * w ^ 3 * (2 * β ^ 3 * w ^ 6 + 2 * β ^ 3 * w ^ 4 - 2 * β ^ 3 * w ^ 2 - 2 * β ^ 3 +
      β ^ 2 * w ^ 6 - 8 * β ^ 2 * w ^ 5 + 5 * β ^ 2 * w ^ 4 - 44 * β ^ 2 * w ^ 3 +
      63 * β ^ 2 * w ^ 2 - 20 * β ^ 2 * w + 3 * β ^ 2 - 5 * β * w ^ 6 + 12 * β * w ^ 5 -
      68 * β * w ^ 4 + 12 * β * w ^ 3 + 32 * β * w ^ 2 - β + 2 * w ^ 6 - 13 * w ^ 5 + 43 * w ^ 4 -
      16 * w ^ 3 - 27 * w ^ 2 - w) * (K ^ 3 * s ^ 3) +
    -4 * w ^ 4 * (6 * β ^ 3 * w ^ 4 - 6 * β ^ 3 + 5 * β ^ 2 * w ^ 4 - 10 * β ^ 2 * w ^ 3 +
      32 * β ^ 2 * w ^ 2 - 18 * β ^ 2 * w + 11 * β ^ 2 - 18 * β * w ^ 4 + 3 * β * w ^ 3 -
      33 * β * w ^ 2 - 3 * β * w - 6 * β + 7 * w ^ 4 - 11 * w ^ 3 + 10 * w ^ 2 - 3 * w +
      1) * (K ^ 4 * s ^ 2) +
    -4 * w ^ 5 * (4 * β ^ 3 * w ^ 2 - 4 * β ^ 3 + 8 * β ^ 2 * w ^ 2 - 4 * β ^ 2 * w + 12 * β ^ 2 -
      19 * β * w ^ 2 - 3 * β * w - 11 * β + 7 * w ^ 2 - 2 * w + 3) * (K ^ 5 * s) +
    -8 * w ^ 6 * (β - 1) * (2 * β - 1) * (K ^ 6))

/-- `twNegEbCertHom` is the homogenization of `twNegEbCertDiff`. -/
private theorem twNegEbCertHom_eq (β w J s t : ℂ) :
    s ^ 6 * twNegEbCertDiff β w J t = twNegEbCertHom β w (s * J) s t := by
  simp only [twNegEbCertHom, twNegEbCertDiff, twNegEbJetT]
  ring

/-- At `J = -(2β + 1)/(2β - 1)` the homogenized difference is a multiple of the node
quadratic. -/
private theorem twNegEbCertHom_node (β w t : ℂ) :
    twNegEbCertHom β w (-(2 * β + 1)) (2 * β - 1) t =
      16 * w ^ 3 * (32 * β ^ 5 * w ^ 4 - 128 * β ^ 5 * w ^ 3 + 192 * β ^ 5 * w ^ 2 -
        128 * β ^ 5 * w + 32 * β ^ 5 - 48 * β ^ 4 * w ^ 4 + 80 * β ^ 4 * w ^ 3 +
        80 * β ^ 4 * w ^ 2 - 112 * β ^ 4 * w + 8 * β ^ 3 * w ^ 4 - 72 * β ^ 3 * w ^ 3 +
        8 * β ^ 3 * w ^ 2 + 72 * β ^ 3 * w - 16 * β ^ 3 + 12 * β ^ 2 * w ^ 4 + 40 * β ^ 2 * w ^ 3 +
        44 * β ^ 2 * w ^ 2 + 16 * β ^ 2 * w - 4 * β * w ^ 4 + 2 * β * w ^ 3 - 6 * β * w ^ 2 -
        10 * β * w + 2 * β - 3 * w ^ 3 + 3 * w) * t *
        (β * (2 * β - 1) * (-w) ^ 2 + (4 * β ^ 2 - 2 * β + 1) * -w + β * (2 * β - 1)) *
        (2 * β - 1) := by
  simp only [twNegEbCertHom]
  ring

/-- The certificate identity at the `E/C_b` node as an identity in `(β, w)`, `w = -x₀`. -/
private theorem twNegEbCertDiff_eq_zero {β w J t : ℂ} (hc : 2 * β - 1 ≠ 0)
    (hJ : (2 * β - 1) * J = -(2 * β + 1))
    (heb : β * (2 * β - 1) * (-w) ^ 2 + (4 * β ^ 2 - 2 * β + 1) * -w + β * (2 * β - 1) = 0) :
    twNegEbCertDiff β w J t = 0 := by
  have h := twNegEbCertHom_eq β w J (2 * β - 1) t
  rw [hJ, twNegEbCertHom_node, heb, mul_zero, zero_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero 6 hc)

/-- The certificate identity at the `E/C_b` node of `P_(-b)`. -/
theorem twNeg_ebNode_cert (b : ℕ) (hb : 1 ≤ b) {m₀ : ℂ}
    (heb : (b : ℂ) * (2 * b - 1) * (m₀ ^ 2) ^ 2 + (4 * b ^ 2 - 2 * b + 1) * m₀ ^ 2 +
      b * (2 * b - 1) = 0) :
    twNegTargetJet b (m₀ ^ 2) (twNegNodeJ b) (-(m₀ ^ 2)) * ((m₀ ^ 2) ^ 2 - 1) =
      2 * m₀ ^ 2 * ((1 - m₀ ^ 2 * twNegNodeJ b) * (m₀ ^ 2 - twNegNodeJ b)) *
        evalIntPoint (derivative (coeffDerivative (twNegTarget b (1 : ℤ)))) (m₀ ^ 2)
          (twNegNodeJ b) := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have h2b : 2 * (b : ℂ) - 1 ≠ 0 := by
    intro h
    have h' : ((2 * b : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      push_cast
      linear_combination h
    have := Nat.cast_injective h'
    omega
  obtain ⟨hζ, hT0⟩ := twNeg_ebNode_zeta b hb heb
  rw [(twNegTarget_one_derivatives_ebNode b hb hζ hT0).2.2]
  have hJ : (2 * (b : ℂ) - 1) * twNegNodeJ b = -(2 * b + 1) := by
    rw [twNegNodeJ]
    field_simp
  generalize twNegNodeJ b = J at hζ hJ ⊢
  generalize m₀ ^ 2 = x at heb hζ ⊢
  obtain ⟨w, rfl⟩ : ∃ w, x = -w := ⟨-x, (neg_neg x).symm⟩
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hb0 h2b (by linear_combination heb)
  rw [neg_neg] at hζ
  obtain ⟨-, hTJ, hTx⟩ := symbolTwistNeg_node_values hζ (by ring) hw0 b
  have hcrit : w + b * ((-w) ^ 2 + 1 - -w * J - w) = 0 := by
    refine mul_left_cancel₀ h2b ?_
    linear_combination heb + b * w * hJ
  have hDJ := dblRootDeriv_mul_of_crit (z₁ := - -w) (α := 2 * -w * J - ((-w) ^ 2 + 1)) (β := 0)
    hb hw0 hcrit
  have hDx := dblRootDeriv_mul_of_crit (z₁ := 2 * -w - J)
    (α := J ^ 2 - 2 * -w * J + 2 * -w + 1) (β := 2 * -w) hb hw0 hcrit
  rw [← hTJ] at hDJ
  rw [← hTx] at hDx
  generalize evalIntPoint (derivative (symbolTwistNeg b)) (-w) J = TJ at hDJ ⊢
  generalize evalIntPoint (coeffDerivative (symbolTwistNeg b)) (-w) J = Tx at hDx ⊢
  have key := twNegEbCertDiff_eq_zero (t := w ^ (b - 1)) h2b hJ heb
  simp only [twNegEbCertDiff, twNegEbJetT] at key
  refine mul_left_cancel₀ (mul_ne_zero (show (6 : ℂ) ≠ 0 by norm_num) (pow_ne_zero 3 hw0)) ?_
  obtain rfl | rfl | ⟨n, rfl⟩ : b = 1 ∨ b = 2 ∨ ∃ n, b = n + 3 := by
    rcases b with _ | _ | _ | n
    · omega
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨n, rfl⟩)
  · simp only [Nat.sub_self, pow_zero, Nat.cast_one] at hDJ hDx key
    simp [twNegTargetJet]
    linear_combination key -
      2 * -w * ((1 - -w * J) * (-w - J)) * (1 - J) * w ^ 2 *
        (2 * -w * J - ((-w) ^ 2 + 1)) * hDx -
      2 * -w * ((1 - -w * J) * (-w - J)) * (1 - J) * w ^ 2 *
        (J ^ 2 - 2 * -w * J + 2 * -w + 1 + 2) * hDJ
  · simp only [show 2 - 1 = 1 from rfl, pow_one, Nat.cast_ofNat] at hDJ hDx key
    simp [twNegTargetJet]
    linear_combination key -
      2 * -w * ((1 - -w * J) * (-w - J)) * (1 - J) * w ^ 2 *
        (2 * -w * J - ((-w) ^ 2 + 1)) * hDx -
      2 * -w * ((1 - -w * J) * (-w - J)) * (1 - J) * w ^ 2 *
        (J ^ 2 - 2 * -w * J + 2 * -w + 1 + 2) * hDJ
  · simp only [show n + 3 - 1 = n + 2 from rfl, Nat.cast_add, Nat.cast_ofNat] at hDJ hDx key
    simp [twNegTargetJet]
    linear_combination key -
      2 * -w * ((1 - -w * J) * (-w - J)) * (1 - J) * w ^ 2 *
        (2 * -w * J - ((-w) ^ 2 + 1)) * hDx -
      2 * -w * ((1 - -w * J) * (-w - J)) * (1 - J) * w ^ 2 *
        (J ^ 2 - 2 * -w * J + 2 * -w + 1 + 2) * hDJ

end AJConjecture
