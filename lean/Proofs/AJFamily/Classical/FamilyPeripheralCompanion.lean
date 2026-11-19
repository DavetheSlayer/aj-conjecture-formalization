import Mathlib
import AJFamily.Classical.SatelliteData

/-!
# Identities in the companion group

Pure group theory in the group `⟨c, d | (cd)^k c = d (cd)^k⟩` of `T(2, 2k+1)`. The staircase
loops of the family word are `famSigma c d s = (dc)^{s/2+1} y_s (dc)^{-(s/2+1)}` (`y_s = c` for
even `s`, `d` for odd `s`), and the closing gap relation is the torus relation
(`torus_of_famSigma`). The products that occur in the strand loops of the family word are
evaluated with the torus relation, using that `Δ = (cd)^k c` swaps `c` and `d` by conjugation
and `Δ² = (cd)^{2k+1}` is central.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The staircase loops: `(dc)^{s/2+1} y (dc)^{-(s/2+1)}`, `y = c` for even `s`, `y = d` for odd `s`. -/
def famSigma (c d : G) (s : ℕ) : G :=
  (d * c) ^ (s / 2 + 1) * (if s % 2 = 0 then c else d) * ((d * c) ^ (s / 2 + 1))⁻¹

/-- `(dc)^k d^{-k}`: the loop collected by the strand `0`. -/
def famG0 (k : ℕ) (c d : G) : G := (d * c) ^ k * (d ^ k)⁻¹

/-- `d⁻¹ c (dc)^{k-1} d c^{-(3k-1)}`: the loop collected by the strand `4k+2`. -/
def famU (k : ℕ) (c d : G) : G := d⁻¹ * c * (d * c) ^ (k - 1) * d * (c ^ (3 * k - 1))⁻¹

/-- The companion part of the product of the strand loops between the two Hopf loops. -/
def famMC (k : ℕ) (c d : G) : G :=
  d * c⁻¹ * (c * d ^ (k - 1) * c⁻¹ * ((c * d) ^ (k - 1))⁻¹) * (d⁻¹ * c) * c ^ (2 * k - 1) *
    (c ^ k * ((c * d) ^ k)⁻¹)

/-- `c (d c)^n = (c d)^n c`. -/
private theorem mul_pow_mul_swap (c d : G) (n : ℕ) : c * (d * c) ^ n = (c * d) ^ n * c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ← mul_assoc, ih]; group

/-- Closed form of `famSigma` at an even index. -/
private theorem famSigma_even (c d : G) (r : ℕ) :
    famSigma c d (2 * r) = (d * c) ^ (r + 1) * c * ((d * c) ^ (r + 1))⁻¹ := by
  simp [famSigma]

/-- Closed form of `famSigma` at an odd index. -/
private theorem famSigma_odd (c d : G) (r : ℕ) :
    famSigma c d (2 * r + 1) = (d * c) ^ (r + 1) * d * ((d * c) ^ (r + 1))⁻¹ := by
  rw [famSigma, show (2 * r + 1) / 2 = r by omega, show (2 * r + 1) % 2 = 1 by omega]
  simp

/-- The staircase recursion `σ (s+1) = d c (σ s)⁻¹`. -/
private theorem famSigma_succ (c d : G) (s : ℕ) :
    famSigma c d (s + 1) = d * c * (famSigma c d s)⁻¹ := by
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' s
  · rw [famSigma_odd, famSigma_even]
    rw [show d * c * ((d * c) ^ (r + 1) * c * ((d * c) ^ (r + 1))⁻¹)⁻¹ =
      d * c * (d * c) ^ (r + 1) * c⁻¹ * ((d * c) ^ (r + 1))⁻¹ by group, ← pow_succ',
      pow_succ (d * c) (r + 1)]
    generalize (d * c) ^ (r + 1) = x
    group
  · rw [show 2 * r + 1 + 1 = 2 * (r + 1) by ring, famSigma_odd, famSigma_even]
    rw [show d * c * ((d * c) ^ (r + 1) * d * ((d * c) ^ (r + 1))⁻¹)⁻¹ =
      d * c * (d * c) ^ (r + 1) * d⁻¹ * ((d * c) ^ (r + 1))⁻¹ by group, ← pow_succ',
      pow_succ (d * c) (r + 1)]
    generalize (d * c) ^ (r + 1) = x
    group

theorem famSigma_of_rec (k : ℕ) (c d : G) (σ : ℕ → G) (h0 : σ 0 = d * c * d⁻¹)
    (hrec : ∀ s, s + 1 ≤ 2 * k - 2 → σ (s + 1) * σ s = d * c) :
    ∀ s, s ≤ 2 * k - 2 → σ s = famSigma c d s := by
  intro s
  induction s with
  | zero => intro _; rw [h0, famSigma_even (r := 0)]; group
  | succ s ih =>
    intro hs
    rw [famSigma_succ, ← ih (by omega), ← hrec s hs]; group

theorem torus_of_famSigma (k : ℕ) (hk : 1 ≤ k) (c d : G)
    (h : famSigma c d (2 * k - 2) = c⁻¹ * d * c) : (c * d) ^ k * c = d * (c * d) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [show 2 * (m + 1) - 2 = 2 * m by omega, famSigma_even] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  have h2 : c * (d * c) ^ (m + 1) * c = d * (c * (d * c) ^ (m + 1)) := by
    rw [mul_assoc, h]; group
  rw [mul_pow_mul_swap] at h2
  have h3 := congrArg (· * c⁻¹) h2
  simpa [mul_assoc] using h3

/-- `d (c d)^n c = (d c)^(n+1)`. -/
private theorem mul_pow_mul_eq_pow_succ (c d : G) (n : ℕ) :
    d * (c * d) ^ n * c = (d * c) ^ (n + 1) := by
  rw [mul_pow_mul_swap, pow_succ, mul_assoc]

theorem evenDesc_famSigma (k : ℕ) (c d : G) :
    ((List.range k).reverse.map fun r ↦ famSigma c d (2 * r)).prod = famG0 k c d := by
  induction k with
  | zero => simp [famG0]
  | succ k ih =>
    rw [List.range_succ, List.reverse_append, List.map_append, List.prod_append, ih]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [famSigma_even, famG0, famG0, pow_succ (d * c) k, pow_succ d k]
    generalize (d * c) ^ k = x
    group

/-- `oddDesc_famSigma` with `k - 1` replaced by `m`. -/
private theorem oddDesc_famSigma_aux (m : ℕ) (c d : G) :
    ((List.range m).reverse.map fun r ↦ famSigma c d (2 * r + 1)).prod =
      (d * c) ^ m * d * (c ^ m)⁻¹ * d⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.reverse_append, List.map_append, List.prod_append, ih]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [famSigma_odd, pow_succ (d * c) m]
    generalize (d * c) ^ m = x
    group

set_option linter.unusedVariables false in
theorem oddDesc_famSigma (k : ℕ) (hk : 1 ≤ k) (c d : G) :
    ((List.range (k - 1)).reverse.map fun r ↦ famSigma c d (2 * r + 1)).prod =
      (d * c) ^ (k - 1) * d * (c ^ (k - 1))⁻¹ * d⁻¹ :=
  oddDesc_famSigma_aux (k - 1) c d

/-- `oddChain_famSigma` with `k - 1` replaced by `m`. -/
private theorem oddChain_famSigma_aux (m : ℕ) (c d : G) :
    ((List.range m).map fun r ↦ d⁻¹ * famSigma c d (2 * r + 1) * c⁻¹).prod =
      c * d ^ m * c⁻¹ * ((c * d) ^ m)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [famSigma_odd, ← mul_pow_mul_eq_pow_succ, pow_succ' (c * d) m]
    generalize (c * d) ^ m = x
    group

set_option linter.unusedVariables false in
theorem oddChain_famSigma (k : ℕ) (hk : 1 ≤ k) (c d : G) :
    ((List.range (k - 1)).map fun r ↦ d⁻¹ * famSigma c d (2 * r + 1) * c⁻¹).prod =
      c * d ^ (k - 1) * c⁻¹ * ((c * d) ^ (k - 1))⁻¹ :=
  oddChain_famSigma_aux (k - 1) c d

theorem evenChain_famSigma (k : ℕ) (c d : G) :
    ((List.range k).map fun r ↦ d⁻¹ * famSigma c d (2 * r) * c⁻¹).prod =
      c ^ k * ((c * d) ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [famSigma_even, ← mul_pow_mul_eq_pow_succ, pow_succ' (c * d) k]
    generalize (c * d) ^ k = x
    group

/-- `famU` in terms of `(c d)^k`. -/
private theorem famU_eq (m : ℕ) (c d : G) :
    famU (m + 1) c d = d⁻¹ * (c * d) ^ (m + 1) * (c ^ (3 * m + 2))⁻¹ := by
  rw [famU, show 3 * (m + 1) - 1 = 3 * m + 2 by omega, Nat.add_sub_cancel,
    show d⁻¹ * c * (d * c) ^ m * d = d⁻¹ * (c * (d * c) ^ m) * d by group, mul_pow_mul_swap,
    pow_succ (c * d) m]
  group

theorem famU_conj (k : ℕ) (hk : 1 ≤ k) (c d : G) (hT : (c * d) ^ k * c = d * (c * d) ^ k) :
    (famU k c d)⁻¹ * d * famU k c d = c := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [famU_eq]
  generalize (c * d) ^ (m + 1) = x at hT ⊢
  obtain rfl : d = x * c * x⁻¹ := by rw [hT]; group
  group

/-- `(d c)^k = d (c d)^k d⁻¹`. -/
private theorem pow_mul_eq_conj (c d : G) (n : ℕ) : (d * c) ^ n = d * (c * d) ^ n * d⁻¹ := by
  rw [mul_pow_mul_swap d c]; group

/-- With `x = (c d)^k` commuting with `c d` and `d = x c x⁻¹`, `Δ² = x c x c` commutes with `c`. -/
private theorem commute_sq_of_comm (x c : G) (h : x * (c * (x * c * x⁻¹)) = c * (x * c * x⁻¹) * x) :
    Commute (x * c * x * c) c := by
  calc x * c * x * c * c = (x * (c * (x * c * x⁻¹))) * x * c := by group
    _ = (c * (x * c * x⁻¹) * x) * x * c := by rw [h]
    _ = c * (x * c * x * c) := by group

theorem famG0_mul_famU (k : ℕ) (hk : 1 ≤ k) (c d : G) (hT : (c * d) ^ k * c = d * (c * d) ^ k) :
    famG0 k c d * famU k c d = compLong k c d := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hcomm : (c * d) ^ (m + 1) * (c * d) = (c * d) * (c * d) ^ (m + 1) := pow_mul_comm' _ _
  rw [famU_eq, famG0, compLong, famDegree, pow_mul_eq_conj,
    show 2 * (m + 1) + 1 = (m + 1) + 1 + (m + 1) by ring, pow_add (c * d) (m + 1 + 1) (m + 1),
    pow_succ (c * d) (m + 1)]
  generalize (c * d) ^ (m + 1) = x at hT hcomm ⊢
  obtain rfl : d = x * c * x⁻¹ := by rw [hT]; group
  have hc := commute_sq_of_comm x c hcomm
  simp only [conj_pow]
  push_cast
  calc _ = (x * c * x * c) * c ^ (-(4 * m + 6 : ℤ)) := by group
    _ = c ^ (-(4 * m + 6 : ℤ)) * (x * c * x * c) := (hc.zpow_right _).eq
    _ = _ := by group

theorem famMC_conj (k : ℕ) (hk : 1 ≤ k) (c d : G) (hT : (c * d) ^ k * c = d * (c * d) ^ k) :
    famG0 k c d * d⁻¹ * famMC k c d * d * (famG0 k c d)⁻¹ = (compLong k c d)⁻¹ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hcomm : (c * d) ^ (m + 1) * (c * d) = (c * d) * (c * d) ^ (m + 1) := pow_mul_comm' _ _
  have hm : (c * d) ^ m = (c * d) ^ (m + 1) * (c * d)⁻¹ := by rw [pow_succ]; group
  rw [famMC, famG0, compLong, famDegree, pow_mul_eq_conj, Nat.add_sub_cancel,
    show 2 * (m + 1) - 1 = 2 * m + 1 by omega, hm,
    show 2 * (m + 1) + 1 = (m + 1) + 1 + (m + 1) by ring, pow_add (c * d) (m + 1 + 1) (m + 1),
    pow_succ (c * d) (m + 1)]
  generalize (c * d) ^ (m + 1) = x at hT hcomm ⊢
  obtain rfl : d = x * c * x⁻¹ := by rw [hT]; group
  have hc := commute_sq_of_comm x c hcomm
  simp only [conj_pow]
  push_cast
  calc _ = (x * c * x * c) * c ^ (-1 : ℤ) * (x * c * x * c)⁻¹ * c ^ (4 * m + 7 : ℤ) *
        (x * c * x * c)⁻¹ := by group
    _ = c ^ (-1 : ℤ) * c ^ (4 * m + 7 : ℤ) * (x * c * x * c)⁻¹ := by
        rw [(hc.zpow_right _).eq]; group
    _ = (x * c * x * c)⁻¹ * c ^ (4 * m + 6 : ℤ) := by
        rw [← zpow_add, (hc.inv_left.zpow_right _).eq]; ring_nf
    _ = _ := by group

end AJConjecture