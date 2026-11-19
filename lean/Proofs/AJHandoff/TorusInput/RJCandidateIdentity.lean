import Mathlib
import AJHandoff.TorusInput.RJSupportSum
import AJConjecture.SkeinTurnbackEigenBasic

/-!
# The candidate traces satisfy the linear relations (node RA5.iv.3)

For even `b = 2n`, `r ≥ 2` and `k ≥ b`:
`∑_N x'_N h_k(N) = θ_b^(r-1) ∑_(j ≤ b) (θ_(b+k-2j)/(θ_b θ_k))^r Δ_(b+k-2j)`, `x'_N =
rjCycleValue b r N`.

Route (a termwise identity). By `rj_sum_cycleValue_mul` (with `φ = id`) the left side is
`(-1)^k θ_b⁻¹ ∑_(i=-n)^n t^(4ri²+4i) [(2ri+1)(k+1)]` (use `[2ri+1] · [(N+1)(k+1)]/[N+1] =
[(2ri+1)(k+1)]` for `N + 1 = |2ri+1|`, `quantumInt` is odd). With `j = n - i` the right side is
`(-1)^k θ_b⁻¹ ∑_(i=-n)^n t^(4ri(k+i+1)) [2i+k+1]` (`θ_(k+2i)/(θ_b θ_k) = t^(4ik+4i²+4i)/θ_b`,
`(-1)^b = 1`). Multiply by `t² - t⁻²`: the `+` monomials agree for the same `i`
(`4ri² + 4i + 2(2ri+1)(k+1) = 4ri(k+i+1) + 2(2i+k+1)`), the `-` monomials agree after
`i ↦ -i` (`Finset.sum_bij` or `Finset.sum_neg_index`-type reflection of `Icc (-n) n`). Numerically
checked (design notes; the identity even holds for every `k`). Estimate 130–200 lines.
-/

noncomputable section

namespace AJConjecture

/-- The kink scalar `θ_b` is not zero. -/
private theorem rj_kinkScalar_ne_zero_candidate (b : ℕ) : kinkScalar b ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ RatFunc.X_ne_zero)

/-- The Hopf scalar at the colour `|m| - 1` of an odd `m = 2ri + 1`, without the absolute
value. -/
private theorem rj_hopf_natAbs_candidate (m : ℤ) (hm : m ≠ 0) (k : ℕ) :
    rjHopf (m.natAbs - 1) k = (-1) ^ k * quantumInt (m * ((k : ℤ) + 1)) / quantumInt m := by
  have hpos : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm
  have hc : (((m.natAbs - 1 : ℕ) : ℤ) + 1) = (m.natAbs : ℤ) := by omega
  rw [rjHopf, hc]
  rcases Int.natAbs_eq m with h | h <;> generalize (m.natAbs : ℤ) = a at h ⊢
  · rw [h]
  · obtain rfl : a = -m := by omega
    rw [neg_mul, claspAlg_quantumInt_neg, claspAlg_quantumInt_neg, mul_neg, neg_div_neg_eq]

/-- A term of the left side of the candidate relation, as a difference of two powers of `t`. -/
private theorem rj_candidate_left_term (b r k : ℕ) (i : ℤ) :
    RatFunc.X ^ (4 * (r : ℤ) * i ^ 2 + 4 * i) * quantumInt (2 * (r : ℤ) * i + 1) / kinkScalar b *
        rjHopf ((2 * (r : ℤ) * i + 1).natAbs - 1) k =
      (-1) ^ k / (kinkScalar b * (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))) *
        ((RatFunc.X : RatFunc ℚ) ^ (4 * (r : ℤ) * i ^ 2 + 4 * i +
            2 * ((2 * (r : ℤ) * i + 1) * ((k : ℤ) + 1))) -
          RatFunc.X ^ (4 * (r : ℤ) * i ^ 2 + 4 * i +
            -(2 * ((2 * (r : ℤ) * i + 1) * ((k : ℤ) + 1))))) := by
  have hm : 2 * (r : ℤ) * i + 1 ≠ 0 := by rw [mul_assoc]; omega
  have hq := claspAlg_quantumInt_ne_zero hm
  have hθ := rj_kinkScalar_ne_zero_candidate b
  have hD := claspAlg_ratFuncX_sq_sub_ne_zero
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  rw [rj_hopf_natAbs_candidate _ hm k]
  have h1 : (RatFunc.X : RatFunc ℚ) ^ (4 * (r : ℤ) * i ^ 2 + 4 * i) *
      quantumInt (2 * (r : ℤ) * i + 1) / kinkScalar b *
        ((-1) ^ k * quantumInt ((2 * (r : ℤ) * i + 1) * ((k : ℤ) + 1)) /
          quantumInt (2 * (r : ℤ) * i + 1)) =
      (-1) ^ k * RatFunc.X ^ (4 * (r : ℤ) * i ^ 2 + 4 * i) *
        quantumInt ((2 * (r : ℤ) * i + 1) * ((k : ℤ) + 1)) / kinkScalar b := by
    field_simp
  rw [h1, quantumInt]
  generalize 4 * (r : ℤ) * i ^ 2 + 4 * i = p
  generalize 2 * ((2 * (r : ℤ) * i + 1) * ((k : ℤ) + 1)) = e
  rw [zpow_add₀ hX, zpow_add₀ hX]
  field_simp

/-- The algebra of one term of the right side, with abstract exponents. -/
private theorem rj_candidate_right_alg (x σ D : RatFunc ℚ) (hx : x ≠ 0) (hD : D ≠ 0)
    (B E c : ℤ) (r : ℕ) (hr : 1 ≤ r) :
    (x ^ B) ^ (r - 1) * ((x ^ E) ^ r * (σ * ((x ^ (2 * c) - x ^ (-(2 * c))) / D))) =
      σ / (x ^ B * D) * (x ^ (B + B * ((r : ℤ) - 1) + E * r + 2 * c) -
        x ^ (B + B * ((r : ℤ) - 1) + E * r + -(2 * c))) := by
  have hr' : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, hr', zpow_add₀ hx, zpow_add₀ hx,
    zpow_add₀ hx, zpow_add₀ hx, zpow_add₀ hx, zpow_add₀ hx]
  have hB : x ^ B ≠ 0 := zpow_ne_zero _ hx
  field_simp

/-- A term of the right side of the candidate relation, as a difference of two powers of `t`
(`i = n - j`). -/
private theorem rj_candidate_right_term (n r k j : ℕ) (i : ℤ) (hr : 1 ≤ r) (hj : j ≤ 2 * n)
    (hk : 2 * n ≤ k) (hi : (n : ℤ) - j = i) :
    kinkScalar (2 * n) ^ (r - 1) *
        (rjTwistRatio (2 * n) k j ^ r * loopScalar (2 * n + k - 2 * j)) =
      (-1) ^ k / (kinkScalar (2 * n) * (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))) *
        ((RatFunc.X : RatFunc ℚ) ^ (4 * (r : ℤ) * i * ((k : ℤ) + i + 1) +
            2 * ((k : ℤ) + 2 * i + 1)) -
          RatFunc.X ^ (4 * (r : ℤ) * i * ((k : ℤ) + i + 1) + -(2 * ((k : ℤ) + 2 * i + 1)))) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hM : ((2 * n + k - 2 * j : ℕ) : ℤ) = k + 2 * i := by omega
  have hs1 : (-1 : RatFunc ℚ) ^ (2 * n) = 1 := Even.neg_one_pow ⟨n, by ring⟩
  have hsM : (-1 : RatFunc ℚ) ^ (2 * n + k - 2 * j) = (-1) ^ k := by
    have h := congrArg (fun e ↦ (-1 : RatFunc ℚ) ^ e)
      (show 2 * n + k - 2 * j + 2 * j = k + 2 * n by omega)
    simp only [pow_add, pow_mul, neg_one_sq, one_pow, mul_one] at h
    exact h
  have hθb : kinkScalar (2 * n) = RatFunc.X ^ ((2 * (n : ℤ)) * (2 * (n : ℤ) + 2)) := by
    rw [kinkScalar, hs1, one_mul]
    push_cast
    rfl
  have hratio : rjTwistRatio (2 * n) k j =
      RatFunc.X ^ ((k + 2 * i) * (k + 2 * i + 2) -
        ((2 * (n : ℤ)) * (2 * (n : ℤ) + 2) + (k : ℤ) * ((k : ℤ) + 2))) := by
    rw [rjTwistRatio, hθb, kinkScalar, kinkScalar, hsM, hM, zpow_sub₀ hX, zpow_add₀ hX]
    have hk1 : (-1 : RatFunc ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  have hΔ : loopScalar (2 * n + k - 2 * j) = (-1) ^ k *
      ((RatFunc.X ^ (2 * ((k : ℤ) + 2 * i + 1)) - RatFunc.X ^ (-(2 * ((k : ℤ) + 2 * i + 1)))) /
        (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))) := by
    rw [loopScalar, hsM, hM, quantumInt]
  rw [hratio, hΔ, hθb, rj_candidate_right_alg _ _ _ hX claspAlg_ratFuncX_sq_sub_ne_zero _ _ _ r hr]
  congr 3 <;> rw [← hi] <;> ring

/-- Reindexing `j ↦ n - j` from `[0, 2n]` to `[-n, n]`. -/
private theorem rj_sum_range_eq_sum_Icc_candidate (n : ℕ) (f : ℤ → RatFunc ℚ) :
    ∑ j ∈ Finset.range (2 * n + 1), f ((n : ℤ) - j) =
      ∑ i ∈ Finset.Icc (-(n : ℤ)) n, f i := by
  refine Finset.sum_nbij' (fun j ↦ (n : ℤ) - j) (fun i ↦ ((n : ℤ) - i).toNat) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_Icc] at hj ⊢
    omega
  · intro i hi
    simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
    omega
  · intro j _
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    omega
  · intro j _
    rfl

/-- The reflection `i ↦ -i` of `[-n, n]`. -/
private theorem rj_sum_Icc_neg_candidate (n : ℕ) (f : ℤ → RatFunc ℚ) :
    ∑ i ∈ Finset.Icc (-(n : ℤ)) n, f (-i) = ∑ i ∈ Finset.Icc (-(n : ℤ)) n, f i := by
  refine Finset.sum_nbij' (fun i ↦ -i) (fun i ↦ -i) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  · intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega
  · intro i _
    simp only [neg_neg]
  · intro i _
    simp only [neg_neg]
  · intro i _
    rfl

/-- The candidate traces satisfy the linear relation for every colour `k ≥ b`. -/
theorem rj_candidate_relation (b r k : ℕ) (hb : Even b) (hr : 2 ≤ r) (hk : b ≤ k) :
    ∑ N ∈ rjSpec b r, rjCycleValue b r N * rjHopf N k =
      kinkScalar b ^ (r - 1) *
        ∑ j ∈ Finset.range (b + 1), rjTwistRatio b k j ^ r * loopScalar (b + k - 2 * j) := by
  have hL := rj_sum_cycleValue_mul b r hb hr (RingHom.id _) (fun N ↦ rjHopf N k)
  simp only [RingHom.id_apply] at hL
  rw [hL]
  obtain ⟨n, rfl⟩ : ∃ n, b = 2 * n := ⟨b / 2, by obtain ⟨m, hm⟩ := hb; omega⟩
  have hn : 2 * n / 2 = n := by omega
  rw [hn, Finset.mul_sum, Finset.sum_congr rfl fun i _ ↦ rj_candidate_left_term (2 * n) r k i,
    Finset.sum_congr rfl fun j hj ↦ rj_candidate_right_term n r k j ((n : ℤ) - j) (by omega)
      (by rw [Finset.mem_range] at hj; omega) hk rfl]
  refine Eq.trans ?_ (rj_sum_range_eq_sum_Icc_candidate n fun i ↦
    (-1) ^ k / (kinkScalar (2 * n) * (RatFunc.X ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ))) *
      ((RatFunc.X : RatFunc ℚ) ^ (4 * (r : ℤ) * i * ((k : ℤ) + i + 1) +
          2 * ((k : ℤ) + 2 * i + 1)) -
        RatFunc.X ^ (4 * (r : ℤ) * i * ((k : ℤ) + i + 1) + -(2 * ((k : ℤ) + 2 * i + 1))))).symm
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← rj_sum_Icc_neg_candidate n fun i ↦
      (RatFunc.X : RatFunc ℚ) ^ (4 * (r : ℤ) * i * ((k : ℤ) + i + 1) +
        -(2 * ((k : ℤ) + 2 * i + 1)))]
  congr 2
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    ring
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    ring

end AJConjecture
