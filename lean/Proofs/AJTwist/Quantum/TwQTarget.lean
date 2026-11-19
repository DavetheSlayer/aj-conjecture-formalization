import Mathlib
import AJTwist.Quantum.TwQWindowCramer
import AJTwist.Quantum.TwQWindowMap
import AJFamily.Quantum.FamTransferMap

/-!
# The pole window and the cleared numerator for every integer index (Unit Q3)

Source: revision 5, Section 3.3 (`transfer.tex`), eq. (adjointnumerator) and the display after
it: `d = 2a + 3` for `a ≥ 0`, `d = 2b + 2` for `a = -b < 0`, and
`𝒩_a = S_(a-1)(𝒜_d) 1 + S_a(𝒜_d)(1 - qJ) - S_(a+1)(𝒜_d)(qJ)`, of degree at most `d` in `J`
("For `a ≥ 1` this follows term by term. At `a = 0`, combine the first and last terms as
`q S_1(𝒜_d)(1 - J)`. For `a = -b` rewrite the numerator as
`q^b {q S_(b+1)(𝒜_d) 1 + S_b(𝒜_d)(1 - qJ) - S_(b-1)(𝒜_d) J}`", using `S_(-k) = q^k S_k`).

`twTarget a q = (q^d x)^(|a|+1) 𝒩_a` is the cleared numerator:

* `a ≥ 1`: the library's `famTarget a q`;
* `a = 0`: `twZeroTarget q = q · (q³x 𝒜_3)(1 - J) + 2 q³ x (1 - qJ)`;
* `a = -b < 0`: `twNegTarget b q`, with `Š_k = twCheb (2b+2) q k`:
  `q^b (q Š_(b+1)(1) + q^d x Š_b(1 - qJ) - (q^d x)² Š_(b-1)(J))`.

The degree bound `natDegree_twTarget_le` and the equality `twTarget a q = (q^d x)^(|a|+1) 𝒩_a`
with the paper's `𝒩_a` were checked at random points for `-4 ≤ a ≤ 4` (scratch
`check_paper_norm.py`); the degree also for `a = ± 6` (scratch `check_transfer.py`).
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- The pole window `d = 2a + 3` for `a ≥ 0` and `d = 2b + 2` for `a = -b < 0`: the order of the
operator `P_a`. -/
def twWindow (a : ℤ) : ℕ :=
  if 0 ≤ a then 2 * a.toNat + 3 else 2 * (-a).toNat + 2

/-- The cleared numerator at `a = 0` (window `3`): `q Š_1(1 - J) + 2 q³ x (1 - qJ)`. -/
def twZeroTarget {R : Type*} [CommRing R] (q : R) : R[X][X] :=
  C (C q) * twAdjoint 3 q (1 - X) + 2 * C (C (q ^ 3) * X) * (1 - C (C q) * X)

/-- The cleared numerator at `a = -b < 0` (window `d = 2b + 2`):
`q^b (q Š_(b+1)(1) + q^d x Š_b(1 - qJ) - (q^d x)² Š_(b-1)(J))`. -/
def twNegTarget {R : Type*} [CommRing R] (b : ℕ) (q : R) : R[X][X] :=
  C (C (q ^ b)) * (C (C q) * twCheb (2 * b + 2) q (b + 1) 1 +
    C (C (q ^ (2 * b + 2)) * X) * twCheb (2 * b + 2) q b (1 - C (C q) * X) -
      C ((C (q ^ (2 * b + 2)) * X) ^ 2) * twCheb (2 * b + 2) q (b - 1) X)

/-- The cleared numerator `(q^d x)^(|a|+1) 𝒩_a` for every integer `a`. -/
def twTarget {R : Type*} [CommRing R] (a : ℤ) (q : R) : R[X][X] :=
  if 1 ≤ a then famTarget a.toNat q
  else if a = 0 then twZeroTarget q
  else twNegTarget (-a).toNat q

theorem twWindow_natCast (m : ℕ) : twWindow (m : ℤ) = 2 * m + 3 := by
  simp [twWindow]

theorem twWindow_zero : twWindow 0 = 3 := by
  simp [twWindow]

theorem twWindow_neg_natCast (b : ℕ) (hb : 1 ≤ b) : twWindow (-(b : ℤ)) = 2 * b + 2 := by
  have h : ¬ (0 : ℤ) ≤ -(b : ℤ) := by omega
  rw [twWindow, ite_eq_right h, neg_neg, Int.toNat_natCast]

theorem three_le_twWindow (a : ℤ) : 3 ≤ twWindow a := by
  unfold twWindow
  split_ifs with h <;> omega

theorem twTarget_natCast {R : Type*} [CommRing R] (m : ℕ) (hm : 1 ≤ m) (q : R) :
    twTarget (m : ℤ) q = famTarget m q := by
  have h : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  simp [twTarget, h]

theorem twTarget_zero {R : Type*} [CommRing R] (q : R) : twTarget 0 q = twZeroTarget q := by
  simp [twTarget]

theorem twTarget_neg_natCast {R : Type*} [CommRing R] (b : ℕ) (hb : 1 ≤ b) (q : R) :
    twTarget (-(b : ℤ)) q = twNegTarget b q := by
  have h1 : ¬ (1 : ℤ) ≤ -(b : ℤ) := by omega
  have h2 : ¬ -(b : ℤ) = 0 := by omega
  rw [twTarget, ite_eq_right h1, ite_eq_right h2, neg_neg, Int.toNat_natCast]

/-- The cleared numerators commute with ring homomorphisms. -/
theorem map_twTarget {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a : ℤ) (q : R) :
    (twTarget a q).map (Polynomial.mapRingHom φ) = twTarget a (φ q) := by
  unfold twTarget
  split_ifs with h1 h0
  · exact map_famTarget φ _ q
  · simp only [twZeroTarget, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
      map_twAdjoint, map_C, map_X, Polynomial.map_one, Polynomial.map_ofNat, coe_mapRingHom,
      Polynomial.map_pow, map_pow]
  · simp only [twNegTarget, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
      map_twCheb, map_C, map_X, Polynomial.map_one, coe_mapRingHom, Polynomial.map_pow,
      map_pow]

/-- The cleared numerator at `a = 0` has degree at most `3` in `J`. -/
private theorem natDegree_twZeroTarget_le_target {R : Type*} [CommRing R] (q : R) :
    (twZeroTarget q).natDegree ≤ 3 := by
  unfold twZeroTarget
  have hlin : (1 - X : R[X][X]).natDegree ≤ 1 := by compute_degree
  have h1 := natDegree_twAdjoint_le 3 q (1 - X) hlin
  have h2 : (2 * C (C (q ^ 3) * X) * (1 - C (C q) * X) : R[X][X]).natDegree ≤ 1 := by
    compute_degree
  exact natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans h1) (h2.trans (by omega))

/-- The cleared numerator at `a = -b` has degree at most `2b + 2` in `J`. -/
private theorem natDegree_twNegTarget_le_target {R : Type*} [CommRing R] (b : ℕ) (q : R) :
    (twNegTarget b q).natDegree ≤ 2 * b + 2 := by
  unfold twNegTarget
  have hlin : (1 - C (C q) * X : R[X][X]).natDegree ≤ 1 := by compute_degree
  have h1 := natDegree_twCheb_le (2 * b + 2) q (b + 1) (1 : R[X][X]) (e := 0)
    (by rw [natDegree_one])
  have h2 := natDegree_twCheb_le (2 * b + 2) q b (1 - C (C q) * X) hlin
  have h3 := natDegree_twCheb_le (2 * b + 2) q (b - 1) (X : R[X][X]) natDegree_X_le
  refine (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans
    (max_le (natDegree_add_le_of_degree_le ?_ ?_) ?_))
  · exact (natDegree_C_mul_le _ _).trans (by omega)
  · exact (natDegree_C_mul_le _ _).trans (by omega)
  · exact (natDegree_C_mul_le _ _).trans (by omega)

/-- The cleared numerator has degree at most the window in `J`. -/
theorem natDegree_twTarget_le {R : Type*} [CommRing R] (a : ℤ) (q : R) :
    (twTarget a q).natDegree ≤ twWindow a := by
  unfold twTarget twWindow
  split_ifs with h1 h0 h2 h3
  · exact natDegree_famTarget_le a.toNat (by omega) q
  · omega
  · exact (natDegree_twZeroTarget_le_target q).trans (by omega)
  · omega
  · omega
  · exact natDegree_twNegTarget_le_target (-a).toNat q

end AJConjecture
