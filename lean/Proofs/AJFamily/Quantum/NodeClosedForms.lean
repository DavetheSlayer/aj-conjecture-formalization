import Mathlib

/-!
# Closed forms at the nodes

Explicit expressions at the two nodes of the family symbol (the abelian node and the E/B node):
basis-polynomial jets, the target jet `famTargetJet`, the double-root solution `dblRootDeriv`, and
the coordinates of the E/B node.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `L₀ = (1 - x₀ J₀)/(J₀ - x₀)` (the Möbius image of `J₀`). -/
def famNodeL (x₀ J₀ : ℂ) : ℂ := (1 - x₀ * J₀) / (J₀ - x₀)

/-- The value `γ = ((1 - x₀)(x₀ - J₀))^d` of the basis polynomials at the node. -/
def famBasisGamma (m : ℕ) (x₀ J₀ : ℂ) : ℂ := ((1 - x₀) * (x₀ - J₀)) ^ (2 * m + 3)

/-- Quadratic coefficient `c = 2J₀/(x₀-J₀) + 2/(1-x₀J₀)` of the basis jets (`= 16m²/(2m+1)` at
the E/B node, `0` at the abelian node). -/
def famBasisJetC (x₀ J₀ : ℂ) : ℂ := 2 * J₀ / (x₀ - J₀) + 2 / (1 - x₀ * J₀)

/-- Linear coefficient of the basis jets. -/
def famBasisJetB (m : ℕ) (x₀ J₀ : ℂ) : ℂ :=
  (4 / (1 - x₀) + (4 * J₀ - 4 * (2 * m + 3) * x₀) / (x₀ - J₀) -
      4 * (2 * m + 3) * x₀ * J₀ / (1 - x₀ * J₀)) -
    (2 * J₀ / (x₀ - J₀) + 2 / (1 - x₀ * J₀))

/-- Constant coefficient of the basis jets. -/
def famBasisJetA (m : ℕ) (x₀ J₀ : ℂ) : ℂ :=
  (2 * (2 * m + 3) * (2 * m + 4) - 4 * (2 * m + 3) ^ 2 * x₀) / (x₀ - 1) +
    (4 * (2 * m + 3) ^ 2 * x₀ * J₀ - 2 * (2 * m + 3) * (2 * m + 2)) / (1 - x₀ * J₀)

/-- The first jet `h₁` of the target polynomial at a node with double point `ζ₀ = 2w`,
`w² = x₀²`, written with the Lucas closed forms of `transferLucas_dual_double`. -/
def famTargetJet (m : ℕ) (x₀ J₀ w : ℂ) : ℂ :=
  let d : ℂ := 2 * m + 3
  let z₁ : ℂ := -8 * d * x₀ ^ 2 - 4 * d * (1 + x₀) - 4 * d * x₀ +
    J₀ * (-8 * d * x₀ + 4 * (d + 1) + 4 * x₀ * (1 + x₀) + 4 * d * x₀ * (1 + x₀) + 4 * d * x₀ ^ 2) -
    (8 + 4 * d) * x₀ * J₀ ^ 2
  let s₁ : ℂ := -(16 * d - 4) * x₀ ^ 2
  let A₀ : ℂ := (1 - J₀) * (x₀ - J₀) * (1 - x₀ * J₀)
  let zJ : ℂ := -1 - x₀ ^ 2 + 2 * x₀ * J₀
  let S : ℕ → ℂ := fun k ↦ 2 * w ^ k
  let S₁ : ℕ → ℂ := fun k ↦ (k : ℂ) ^ 2 * w ^ (k - 1) * z₁ - (k : ℂ) * ((k : ℂ) - 1) * w ^ (k - 2) * s₁
  let Sd : ℕ → ℂ := fun k ↦ (k : ℂ) ^ 2 * w ^ (k - 1)
  let Sh : ℕ → ℂ := fun k ↦ (k : ℂ) ^ 2 * ((k : ℂ) ^ 2 - 1) / 12 * w ^ (k - 2)
  x₀ ^ 2 * S₁ (m - 1) - 16 * d * x₀ ^ 2 * S (m - 1) + 4 * A₀ * x₀ ^ 2 * Sh (m - 1) * zJ +
    x₀ * (1 - J₀) * S₁ m + (4 * J₀ - 8 * d * (1 - J₀)) * x₀ * S m +
    4 * A₀ * x₀ * (-Sd m + Sh m * zJ * (1 - J₀)) -
    J₀ * S₁ (m + 1) + 4 * J₀ * S (m + 1) - 4 * A₀ * (Sd (m + 1) + Sh (m + 1) * zJ * J₀)

/-- Closed form of `z_k` for `z_(k+2) = 2w z_(k+1) - w² z_k + α y_(k+1) - β y_k`, `z₀ = 0`,
`y_k = w^k + k w^(k-1) δ`. -/
def dblRootDeriv (w δ z₁ α β : ℂ) (k : ℕ) : ℂ :=
  w ^ k * ((k : ℂ) * (z₁ / w) + (α * w * (w + δ) - β * w) / w ^ 3 * ((k : ℂ) * ((k : ℂ) - 1) / 2) +
    δ * (α * w - β) / w ^ 3 * ((k : ℂ) * ((k : ℂ) - 1) * ((k : ℂ) - 2) / 6))

/-- `J₀ = -(2m-1)/(2m+1)` at the E/B node. -/
def ebNodeJ (m : ℕ) : ℂ := -(2 * (m : ℂ) - 1) / (2 * m + 1)

/-- `L₀` at the E/B node over `M = m₀`. -/
def ebNodeL (m : ℕ) (m₀ : ℂ) : ℂ := famNodeL (m₀ ^ 2) (ebNodeJ m)

end AJConjecture
