import Mathlib
import AJConjecture.APolynomial
import AJHandoff.LocalTheory.LocOpJets

/-!
# Residual blocks, allowed transverse mixed nodes and the allocation index (4)

The residual symbol `P₀ ∈ ℂ[z][u]` of `P` factors over `ℂ(z)` into residual blocks: up to
scalars `κ₁, κ₂ ∈ ℂ[z]`, `κ₁ P₀ = κ₂ ∏ B_i` with each `B_i` irreducible over `ℂ(z)` and distinct
blocks not associated (so `P₀` is square-free). A point `p = (z₀, λ)` is evaluated by
`evalPoint B p = B(z₀, λ)`; `derivative` is `∂_u` and `innerDerivative` is `∂_z`.

An allowed transverse mixed node of the blocks `G = B g`, `H = B h` (Section 4 of the source)
is a point with `z₀ λ ≠ 0`, `G = H = 0`, `G_u H_u ≠ 0`, `J = G_u H_z - H_u G_z ≠ 0`, no other
block vanishing there, no two distinct blocks meeting anywhere else on the whole fibre `z = z₀`
(self-collisions inside one block are allowed), and the leading and constant coefficients of `P`
not vanishing at `(h, z) = (0, z₀)` (this is (JL) for the companion of the monic normalization
of `P`: no endpoint is lost).

With `T = ∏_{i ≠ g, h} B_i` and `v₀ = c z₀`, formula (4) of the source is
`I_G = -[P₁/T - λ v₀ H_u G_z] / [v₀ λ (G_u H_z - H_u G_z)]` at `(z₀, λ)` for monic `P`, `P₀ = GHT`.
For `P` normalized by `κ₁ P₀ = κ₂ G H T` the quotient `P₁/T` of the monic normalization is
`κ₁ P₁ / (κ₂ T)`. Interchanging `G` and `H` gives `I_H = -1 - I_G` (formula (5)).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- `G` divides `F` over `ℂ(z)`. -/
def LocBlockDvd (G F : ℂ[X][X]) : Prop :=
  G.map (algebraMap ℂ[X] (RatFunc ℂ)) ∣ F.map (algebraMap ℂ[X] (RatFunc ℂ))

/-- `B` is a decomposition of the residual symbol of `P` into residual blocks: irreducible over
`ℂ(z)`, pairwise not associated, with product `P₀` up to nonzero scalars of `ℂ[z]`. -/
structure LocResidualBlocks (P : LocOp) {ι : Type*} [Fintype ι] (B : ι → ℂ[X][X]) : Prop where
  exists_eq : ∃ κ₁ κ₂ : ℂ[X], κ₁ ≠ 0 ∧ κ₂ ≠ 0 ∧ C κ₁ * opJet0 P = C κ₂ * ∏ i, B i
  irreducible : ∀ i, Irreducible ((B i).map (algebraMap ℂ[X] (RatFunc ℂ)))
  not_associated : ∀ i j, i ≠ j →
    ¬ Associated ((B i).map (algebraMap ℂ[X] (RatFunc ℂ))) ((B j).map (algebraMap ℂ[X] (RatFunc ℂ)))

/-- The cofactor `T = ∏_{i ≠ g, h} B_i`. -/
def locCofactor {ι : Type*} [Fintype ι] [DecidableEq ι] (B : ι → ℂ[X][X]) (g h : ι) :
    ℂ[X][X] :=
  ∏ i ∈ (Finset.univ.erase g).erase h, B i

/-- An allowed transverse mixed node of `B g` and `B h` at `(z₀, λ)`, with normalizing scalars
`κ₁ P₀ = κ₂ ∏ B_i` that are units at `z₀`. -/
structure LocAllowedNode (P : LocOp) {ι : Type*} [Fintype ι] (B : ι → ℂ[X][X])
    (κ₁ κ₂ : ℂ[X]) (g h : ι) (z₀ lam : ℂ) : Prop where
  sym : C κ₁ * opJet0 P = C κ₂ * ∏ i, B i
  κ₁_ne : κ₁.eval z₀ ≠ 0
  κ₂_ne : κ₂.eval z₀ ≠ 0
  ne : g ≠ h
  z₀_ne : z₀ ≠ 0
  lam_ne : lam ≠ 0
  natDegree_eq : (opJet0 P).natDegree = P.natDegree
  lead_ne : (opJet0 P).leadingCoeff.eval z₀ ≠ 0
  const_ne : ((opJet0 P).coeff 0).eval z₀ ≠ 0
  root_g : evalPoint (B g) (z₀, lam) = 0
  root_h : evalPoint (B h) (z₀, lam) = 0
  du_g : evalPoint (derivative (B g)) (z₀, lam) ≠ 0
  du_h : evalPoint (derivative (B h)) (z₀, lam) ≠ 0
  jac : evalPoint (derivative (B g)) (z₀, lam) * evalPoint (innerDerivative (B h)) (z₀, lam) -
      evalPoint (derivative (B h)) (z₀, lam) * evalPoint (innerDerivative (B g)) (z₀, lam) ≠ 0
  other : ∀ i, i ≠ g → i ≠ h → evalPoint (B i) (z₀, lam) ≠ 0
  fibre : ∀ i j, i ≠ j → ∀ l : ℂ, evalPoint (B i) (z₀, l) = 0 → evalPoint (B j) (z₀, l) = 0 →
    l = lam ∧ ((i = g ∧ j = h) ∨ (i = h ∧ j = g))

/-- Formula (4): the allocation index `I_G` of the right factor containing `G` and not `H`. -/
def locNodeIndex (c z₀ lam : ℂ) (P₁ G H T : ℂ[X][X]) (κ₁ κ₂ : ℂ[X]) : ℂ :=
  -((κ₁.eval z₀ * evalPoint P₁ (z₀, lam)) / (κ₂.eval z₀ * evalPoint T (z₀, lam)) -
      lam * (c * z₀) * evalPoint (derivative H) (z₀, lam) *
        evalPoint (innerDerivative G) (z₀, lam)) /
    (c * z₀ * lam * (evalPoint (derivative G) (z₀, lam) * evalPoint (innerDerivative H) (z₀, lam) -
      evalPoint (derivative H) (z₀, lam) * evalPoint (innerDerivative G) (z₀, lam)))

theorem LocAllowedNode.symm {P : LocOp} {ι : Type*} [Fintype ι] {B : ι → ℂ[X][X]}
    {κ₁ κ₂ : ℂ[X]} {g h : ι} {z₀ lam : ℂ} (hn : LocAllowedNode P B κ₁ κ₂ g h z₀ lam) :
    LocAllowedNode P B κ₁ κ₂ h g z₀ lam where
  sym := hn.sym
  κ₁_ne := hn.κ₁_ne
  κ₂_ne := hn.κ₂_ne
  ne := hn.ne.symm
  z₀_ne := hn.z₀_ne
  lam_ne := hn.lam_ne
  natDegree_eq := hn.natDegree_eq
  lead_ne := hn.lead_ne
  const_ne := hn.const_ne
  root_g := hn.root_h
  root_h := hn.root_g
  du_g := hn.du_h
  du_h := hn.du_g
  jac := by
    intro h0
    exact hn.jac (by linear_combination -h0)
  other := fun i hi hi' ↦ hn.other i hi' hi
  fibre := fun i j hij l hi hj ↦ by
    obtain ⟨hl, hc⟩ := hn.fibre i j hij l hi hj
    exact ⟨hl, by tauto⟩

/-- Formula (5): `I_H = -1 - I_G`. -/
theorem locNodeIndex_swap {c z₀ lam : ℂ} {P₁ G H T : ℂ[X][X]} {κ₁ κ₂ : ℂ[X]} (hc : c ≠ 0)
    (hz₀ : z₀ ≠ 0) (hlam : lam ≠ 0)
    (hJ : evalPoint (derivative G) (z₀, lam) * evalPoint (innerDerivative H) (z₀, lam) -
      evalPoint (derivative H) (z₀, lam) * evalPoint (innerDerivative G) (z₀, lam) ≠ 0) :
    locNodeIndex c z₀ lam P₁ H G T κ₁ κ₂ = -1 - locNodeIndex c z₀ lam P₁ G H T κ₁ κ₂ := by
  have hJ' : evalPoint (derivative H) (z₀, lam) * evalPoint (innerDerivative G) (z₀, lam) -
      evalPoint (derivative G) (z₀, lam) * evalPoint (innerDerivative H) (z₀, lam) ≠ 0 := by
    intro h0
    exact hJ (by linear_combination -h0)
  unfold locNodeIndex
  field_simp
  ring

theorem locCofactor_swap {ι : Type*} [Fintype ι] [DecidableEq ι] (B : ι → ℂ[X][X]) (g h : ι) :
    locCofactor B h g = locCofactor B g h := by
  unfold locCofactor
  rw [Finset.erase_right_comm]

end AJConjecture
