import Mathlib
import AJConjecture.QAlgCycloStep
import AJHandoff.TorusQuantum.PairQFormula

/-!
# The inner operator `p_a` for every integer index (Unit Q4)

Source: revision 5, Section 3.2 (`transfer.tex`, "Transport in the companion channel"),
eq. (innerforcing): `p_a = S_(a-1)(𝒵) + (1 - qJ) S_a(𝒵) - qJ S_(a+1)(𝒵)` for every integer `a`,
with the trace polynomials `S_0 = 2`, `S_1 = Z`, `S_(k+1) = Z S_k - q⁻¹ S_(k-1)` "extended to
integer `k`", so that `S_k(Q + \hat Q) = Q^k + \hat Q^k` and `S_(-k) = q^k S_k`.

* `twChebZ k` is `S_k(V)` for `k ∈ ℤ` on sequences in `j` (`V = cycloStep` is the library's `𝒵`,
  `cycloCheb` its trace operators for `k ≥ 0`).
* `twDefect a u = p_a D`, `D = pairQCycloCoeff u`. For `a = m ≥ 1` it is the library's
  `pairQCycloDefect m u`; for `a = 0` it is `q (1 - J) V D + 2 (1 - qJ) D`; for `a = -b < 0` it
  is `q^b (q S_(b+1)(V) + (1 - qJ) S_b(V) - J S_(b-1)(V)) D`.
-/

noncomputable section

namespace AJConjecture

/-- The trace operator `S_k(V)` for an integer index: `S_(-k) = q^k S_k`. -/
def twChebZ (k : ℤ) (y : ℕ → RatFunc ℚ) (j : ℕ) : RatFunc ℚ :=
  if 0 ≤ k then cycloCheb k.toNat y j else qParam ^ (-k) * cycloCheb (-k).toNat y j

/-- The inner operator `p_a = S_(a-1)(V) + (1 - qJ) S_a(V) - qJ S_(a+1)(V)` applied to the
cyclotomic coefficients of `u` (eq. (innerforcing)). -/
def twDefect (a : ℤ) (u : ℕ → RatFunc ℚ) (j : ℕ) : RatFunc ℚ :=
  twChebZ (a - 1) (pairQCycloCoeff u) j
    + (1 - qParam * qParam ^ j) * twChebZ a (pairQCycloCoeff u) j
    - qParam * qParam ^ j * twChebZ (a + 1) (pairQCycloCoeff u) j

theorem twChebZ_natCast (k : ℕ) (y : ℕ → RatFunc ℚ) (j : ℕ) :
    twChebZ (k : ℤ) y j = cycloCheb k y j := by
  rw [twChebZ, ite_eq_left (Int.natCast_nonneg k), Int.toNat_natCast]

theorem twChebZ_neg_natCast (k : ℕ) (y : ℕ → RatFunc ℚ) (j : ℕ) :
    twChebZ (-(k : ℤ)) y j = qParam ^ k * cycloCheb k y j := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.cast_zero, neg_zero, twChebZ, ite_eq_left le_rfl, pow_zero, one_mul, Int.toNat_zero]
  · rw [twChebZ, ite_eq_right (by omega), neg_neg, Int.toNat_natCast, zpow_natCast]

/-- For `a = m ≥ 1` the inner operator gives the library's defect. -/
theorem twDefect_natCast (m : ℕ) (hm : 1 ≤ m) (u : ℕ → RatFunc ℚ) :
    twDefect (m : ℤ) u = pairQCycloDefect m u := by
  funext j
  have h1 : ((m : ℤ) - 1) = ((m - 1 : ℕ) : ℤ) := by omega
  have h2 : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by omega
  rw [twDefect, pairQCycloDefect, h1, h2, twChebZ_natCast, twChebZ_natCast, twChebZ_natCast]

/-- The inner operator at `a = 0`: `q (1 - J) V D + 2 (1 - qJ) D`. -/
theorem twDefect_zero (u : ℕ → RatFunc ℚ) (j : ℕ) :
    twDefect 0 u j =
      qParam * (1 - qParam ^ j) * cycloStep (pairQCycloCoeff u) j +
        2 * (1 - qParam * qParam ^ j) * pairQCycloCoeff u j := by
  have h1 : ((0 : ℤ) - 1) = -((1 : ℕ) : ℤ) := by omega
  have h2 : ((0 : ℤ) + 1) = ((1 : ℕ) : ℤ) := by omega
  have h3 : (0 : ℤ) = ((0 : ℕ) : ℤ) := by omega
  rw [twDefect, h1, h2, twChebZ_neg_natCast, twChebZ_natCast, h3, twChebZ_natCast]
  simp only [cycloCheb]
  ring

/-- The inner operator at `a = -b < 0`:
`q^b (q S_(b+1)(V) + (1 - qJ) S_b(V) - J S_(b-1)(V)) D`. -/
theorem twDefect_neg_natCast (b : ℕ) (hb : 1 ≤ b) (u : ℕ → RatFunc ℚ) (j : ℕ) :
    twDefect (-(b : ℤ)) u j =
      qParam ^ b * (qParam * cycloCheb (b + 1) (pairQCycloCoeff u) j +
        (1 - qParam * qParam ^ j) * cycloCheb b (pairQCycloCoeff u) j -
          qParam ^ j * cycloCheb (b - 1) (pairQCycloCoeff u) j) := by
  have h1 : (-(b : ℤ) - 1) = -((b + 1 : ℕ) : ℤ) := by omega
  have h2 : (-(b : ℤ) + 1) = -((b - 1 : ℕ) : ℤ) := by omega
  rw [twDefect, h1, h2, twChebZ_neg_natCast, twChebZ_neg_natCast, twChebZ_neg_natCast]
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

end AJConjecture
