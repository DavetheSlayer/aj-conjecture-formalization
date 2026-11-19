import Mathlib
import AJTwist.Quantum.TwQWindowMap

/-!
# The cleared target of an inner relation

Source: revision 5, Section 3.3 (`transfer.tex`), eq. (adjoint), (adjointnumerator): the adjoint
`𝒜_d` of `𝒵` in the sum against the kernel of a pole window `d`, and the cleared numerator of an
inner operator. There the inner operator is `p_a` and the window is `d(a)`; here it is an
arbitrary operator `∑_{s ≤ r} ρ_s(J) V^s` with polynomial coefficients, and the window `d` is
any integer with `d ≥ deg ρ_s + 2s` for all `s`.

`twHTarget d q r ρ = ∑_{s ≤ r} (q^d x)^(r-s) (q^d x 𝒜_d)^s (ρ_s)` is the cleared numerator
`(q^d x)^r ∑_s 𝒜_d^s(ρ_s)` (`twAdjoint d q = q^d x 𝒜_d` is the library's cleared adjoint), a
polynomial in `J` (outer variable) and `x` (inner variable).

* `natDegree_twHTarget_le`: its degree in `J` is at most `d` when `deg ρ_s + 2s ≤ d` for all
  `s ≤ r` (`natDegree_twAdjoint_le`: the adjoint raises the degree in `J` by at most two);
* `map_twHTarget`: naturality in the ring (`map_twAdjoint`), used with `twTHom : ℤ[t] → ℚ(t)`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The cleared numerator `∑_{s ≤ r} (q^d x)^(r-s) (twAdjoint d q)^[s] ρ_s` of the inner
operator `∑_{s ≤ r} ρ_s(J) V^s` in the pole window `d`. -/
def twHTarget {R : Type*} [CommRing R] (d : ℕ) (q : R) (r : ℕ) (ρ : ℕ → R[X]) : R[X][X] :=
  ∑ s ∈ Finset.range (r + 1),
    C (C (q ^ d) * X) ^ (r - s) * (twAdjoint d q)^[s] ((ρ s).map C)

/-- The iterated cleared adjoint raises the degree in `J` by at most `2s`. -/
theorem twH_natDegree_iterate_twAdjoint_le {R : Type*} [CommRing R] (d : ℕ) (q : R) (s : ℕ)
    (n : R[X][X]) {e : ℕ} (hn : n.natDegree ≤ e) :
    ((twAdjoint d q)^[s] n).natDegree ≤ e + 2 * s := by
  induction s with
  | zero => exact hn
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    exact (natDegree_twAdjoint_le d q _ ih).trans (by omega)

/-- The cleared target has degree at most `d` in `J` when `deg ρ_s + 2s ≤ d` for `s ≤ r`. -/
theorem natDegree_twHTarget_le {R : Type*} [CommRing R] (d : ℕ) (q : R) (r : ℕ) (ρ : ℕ → R[X])
    (hd : ∀ s, s ≤ r → (ρ s).natDegree + 2 * s ≤ d) : (twHTarget d q r ρ).natDegree ≤ d := by
  refine natDegree_sum_le_of_forall_le _ _ fun s hs ↦ ?_
  rw [← C_pow]
  refine (natDegree_C_mul_le _ _).trans ?_
  exact (twH_natDegree_iterate_twAdjoint_le d q s _ natDegree_map_le).trans
    (hd s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)))

/-- The iterated cleared adjoint commutes with ring homomorphisms. -/
theorem twH_map_iterate_twAdjoint {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (d : ℕ) (q : R) (s : ℕ) (n : R[X][X]) :
    ((twAdjoint d q)^[s] n).map (Polynomial.mapRingHom φ) =
      (twAdjoint d (φ q))^[s] (n.map (Polynomial.mapRingHom φ)) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_twAdjoint, ih]

/-- The cleared target commutes with ring homomorphisms. -/
theorem map_twHTarget {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (q : R)
    (r : ℕ) (ρ : ℕ → R[X]) :
    (twHTarget d q r ρ).map (Polynomial.mapRingHom φ) =
      twHTarget d (φ q) r (fun s ↦ (ρ s).map φ) := by
  have hC : ∀ a : R[X], (a.map C).map (Polynomial.mapRingHom φ) = (a.map φ).map C := by
    intro a
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext x
    simp
  simp only [twHTarget, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C,
    map_X, coe_mapRingHom, map_pow, twH_map_iterate_twAdjoint, hC]

end AJConjecture
