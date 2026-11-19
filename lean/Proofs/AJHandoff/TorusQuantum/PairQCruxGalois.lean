import Mathlib

/-!
# Traces of powers of a matrix of finite order (route node of the crux)

Stage RA4 of the proposed route to `pairQ_torusInput` (design notes): on the isotypic component
`P_N` of `f_b^{⊗ r}` the cabled cyclic braid `c = σ_0 ⋯ σ_(r-2)` satisfies `c^r = μ_N`; after
the field embedding `t ↦ t^r`, `μ_N = ν_N^r` and `A = ν_N⁻¹ c P_N + (1 - P_N)` has `A^r = 1`.
The lemma below gives `tr(W A^s) = tr(W A)` for `s` coprime to `r`, hence
`tr_q(c^s P_N) = ν_N^(s-1) tr_q(c P_N)` (the Rosso–Jones argument), the weight `W` being the
diagonal matrix of the quantum trace, which commutes with `c` and `P_N`.

Proof idea: `X^r - 1` is separable in characteristic `0`, so `A` is semisimple; the space splits
into the `Φ_d`-primary parts, `d ∣ r`, each preserved by the diagonal `W` and the coordinate
blocks of its eigenvalues; on a `Φ_d`-primary part `A` is multiplication by a root `ζ` of the
irreducible `Φ_d` on a `K(ζ)`-vector space, and `Tr_(K(ζ)/K)(ζ^s) = Tr_(K(ζ)/K)(ζ)` because
`ζ ↦ ζ^s` is a `K`-automorphism of `K(ζ)` (`Φ_d` irreducible over `K`, `gcd(s, d) = 1`).
`pairQ_irreducible_cyclotomic_ratFunc` supplies the irreducibility over `ℚ(t)`: `ℚ` is
algebraically closed in `ℚ(t)` and `Φ_d` is irreducible over `ℚ`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Shifting the summation index of an `r`-periodic sequence over `range r`. -/
private theorem pairQ_sum_range_shift {M : Type*} [AddCommGroup M] (g : ℕ → M) (r : ℕ)
    (h : g r = g 0) : ∑ k ∈ Finset.range r, g (k + 1) = ∑ k ∈ Finset.range r, g k := by
  have h1 := Finset.sum_range_succ' g r
  rw [Finset.sum_range_succ, h] at h1
  exact (add_right_cancel h1).symm

section SpecProj

variable {L : Type*} [Field L] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The spectral projector `P_j = r⁻¹ ∑_(k<r) η^(jk) B^k`. -/
private def pairQSpecProj (B : Matrix ι ι L) (r : ℕ) (η : L) (j : ℕ) : Matrix ι ι L :=
  (r : L)⁻¹ • ∑ k ∈ Finset.range r, (η ^ (j * k)) • B ^ k

/-- `B P_j = ζ^j P_j` when `B^r = 1`, `η^r = 1` and `ζ η = 1`. -/
private theorem pairQSpecProj_mul_left (B : Matrix ι ι L) (r : ℕ) (ζ η : L) (hB : B ^ r = 1)
    (hη : η ^ r = 1) (hζη : ζ * η = 1) (j : ℕ) :
    B * pairQSpecProj B r η j = ζ ^ j • pairQSpecProj B r η j := by
  have h := pairQ_sum_range_shift (fun k ↦ (ζ ^ j * η ^ (j * k)) • B ^ k) r (by
    show (ζ ^ j * η ^ (j * r)) • B ^ r = (ζ ^ j * η ^ (j * 0)) • B ^ 0
    rw [mul_comm j r, pow_mul, hη, one_pow, hB, mul_zero, pow_zero, pow_zero])
  have hS : B * ∑ k ∈ Finset.range r, (η ^ (j * k)) • B ^ k =
      ζ ^ j • ∑ k ∈ Finset.range r, (η ^ (j * k)) • B ^ k := by
    rw [Finset.smul_sum]
    simp only [← smul_smul] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Matrix.mul_smul, ← pow_succ', smul_smul]
    congr 1
    rw [mul_add, pow_add, mul_one, mul_comm (η ^ (j * k)), ← mul_assoc, ← mul_pow, hζη, one_pow,
      one_mul]
  rw [pairQSpecProj, Matrix.mul_smul, hS, smul_comm]

/-- `B^k P_j = ζ^(jk) P_j`. -/
private theorem pairQSpecProj_pow_mul (B : Matrix ι ι L) (r : ℕ) (ζ η : L) (hB : B ^ r = 1)
    (hη : η ^ r = 1) (hζη : ζ * η = 1) (j k : ℕ) :
    B ^ k * pairQSpecProj B r η j = ζ ^ (j * k) • pairQSpecProj B r η j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_smul,
      pairQSpecProj_mul_left B r ζ η hB hη hζη, smul_smul, ← pow_add]
    ring_nf

/-- The spectral projectors are idempotent. -/
private theorem pairQSpecProj_idem [CharZero L] (B : Matrix ι ι L) (r : ℕ) (hr : 0 < r) (ζ η : L)
    (hB : B ^ r = 1) (hη : η ^ r = 1) (hζη : ζ * η = 1) (j : ℕ) :
    pairQSpecProj B r η j * pairQSpecProj B r η j = pairQSpecProj B r η j := by
  set P := pairQSpecProj B r η j with hP
  have hk : ∀ k, B ^ k * P = ζ ^ (j * k) • P := pairQSpecProj_pow_mul B r ζ η hB hη hζη j
  have h : ∀ k ∈ Finset.range r, η ^ (j * k) * ζ ^ (j * k) = 1 := fun k _ ↦ by
    rw [← mul_pow, mul_comm, hζη, one_pow]
  calc P * P = ((r : L)⁻¹ • ∑ k ∈ Finset.range r, (η ^ (j * k)) • B ^ k) * P := rfl
    _ = (r : L)⁻¹ • ∑ k ∈ Finset.range r, (η ^ (j * k) * ζ ^ (j * k)) • P := by
      rw [Matrix.smul_mul, Finset.sum_mul]
      simp only [Matrix.smul_mul, hk, smul_smul]
    _ = P := by
      rw [Finset.sum_congr rfl fun k hk ↦ by rw [h k hk], Finset.sum_const, Finset.card_range,
        one_smul, ← Nat.cast_smul_eq_nsmul L, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hr.ne'), one_smul]

/-- The spectral projectors sum to `1` when `η` is a primitive `r`-th root of unity. -/
private theorem pairQSpecProj_sum [CharZero L] (B : Matrix ι ι L) (r : ℕ) (hr : 0 < r) (η : L)
    (hη : IsPrimitiveRoot η r) :
    ∑ j ∈ Finset.range r, pairQSpecProj B r η j = 1 := by
  unfold pairQSpecProj
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [Finset.sum_eq_single 0]
  · simp only [mul_zero, pow_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hr.ne'), one_smul]
  · intro k hk hk0
    rw [Finset.mem_range] at hk
    have hne : η ^ k ≠ 1 := hη.pow_ne_one_of_pos_of_lt hk0 hk
    have hs : ∑ j ∈ Finset.range r, η ^ (j * k) = 0 := by
      simp only [mul_comm _ k, pow_mul]
      rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hη.pow_eq_one, one_pow, sub_self,
        zero_div]
    rw [hs, zero_smul]
  · intro h; exact absurd (Finset.mem_range.mpr hr) h

end SpecProj

/-- Multiplication by a unit modulo `r` permutes `range r`. -/
private theorem pairQ_sum_range_mul_mod {M : Type*} [AddCommMonoid M] (h : ℕ → M) (r s : ℕ)
    (hs : Nat.Coprime s r) :
    ∑ j ∈ Finset.range r, h (j * s % r) = ∑ j ∈ Finset.range r, h j := by
  have hinj : Set.InjOn (fun j ↦ j * s % r) (Finset.range r : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    exact (Nat.ModEq.cancel_right_of_coprime (by rw [Nat.gcd_comm]; exact hs) hab).eq_of_lt_of_lt
      ha hb
  have himg : (Finset.range r).image (fun j ↦ j * s % r) = Finset.range r := by
    refine Finset.eq_of_subset_of_card_le (fun x hx ↦ ?_) ?_
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (Nat.mod_lt _ (by
        have := Finset.mem_range.mp hj; omega))
    · rw [Finset.card_image_of_injOn hinj]
  rw [← Finset.sum_image (f := h) hinj, himg]

section SpecProjTrace

variable {L : Type*} [Field L] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `tr(W B^k) = ∑_j ζ^(jk) tr(W P_j)`. -/
private theorem pairQ_trace_mul_pow_eq_sum [CharZero L] (B W : Matrix ι ι L) (r : ℕ) (hr : 0 < r)
    (ζ η : L) (hB : B ^ r = 1) (hη : IsPrimitiveRoot η r) (hζη : ζ * η = 1) (k : ℕ) :
    (W * B ^ k).trace =
      ∑ j ∈ Finset.range r, ζ ^ (j * k) * (W * pairQSpecProj B r η j).trace := by
  rw [← Matrix.mul_one (B ^ k), ← pairQSpecProj_sum B r hr η hη, Finset.mul_sum, Finset.mul_sum,
    Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [pairQSpecProj_pow_mul B r ζ η hB hη.pow_eq_one hζη, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul]

/-- `tr(W P_j) = r⁻¹ ∑_k η^(jk) tr(W B^k)`. -/
private theorem pairQ_trace_mul_specProj (B W : Matrix ι ι L) (r : ℕ) (η : L) (j : ℕ) :
    (W * pairQSpecProj B r η j).trace =
      (r : L)⁻¹ * ∑ k ∈ Finset.range r, η ^ (j * k) * (W * B ^ k).trace := by
  rw [pairQSpecProj, Matrix.mul_smul, Matrix.trace_smul, Finset.mul_sum, Matrix.trace_sum,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

end SpecProjTrace

/-- The trace of an idempotent matrix is the dimension of its range. -/
private theorem pairQ_trace_idem_eq_finrank {L ι : Type*} [Field L] [Fintype ι] [DecidableEq ι]
    (E : Matrix ι ι L) (hE : E * E = E) :
    E.trace = (Module.finrank L (LinearMap.range (Matrix.toLin' E)) : L) := by
  have hi : IsIdempotentElem (Matrix.toLin' E) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]
  rw [← (LinearMap.IsIdempotentElem.isProj_range _ hi).trace, Matrix.trace_toLin'_eq]

/-- For an idempotent `P` commuting with the coordinate blocks of a diagonal `w` over `K`, the
weighted trace `tr(diag(φ ∘ w) P)` comes from `K`. -/
private theorem pairQ_trace_diagonal_mul_idem_mem {K L ι : Type*} [Field K] [Field L] [Fintype ι]
    [DecidableEq ι] [DecidableEq K] (φ : K →+* L) (w : ι → K) (P : Matrix ι ι L)
    (hP : P * P = P)
    (hQ : ∀ μ : K, Matrix.diagonal (fun i ↦ if w i = μ then (1 : L) else 0) * P =
      P * Matrix.diagonal (fun i ↦ if w i = μ then (1 : L) else 0)) :
    ∃ x : K, (Matrix.diagonal (fun i ↦ φ (w i)) * P).trace = φ x := by
  set Q : K → Matrix ι ι L := fun μ ↦ Matrix.diagonal (fun i ↦ if w i = μ then (1 : L) else 0)
  have hQQ : ∀ μ, Q μ * Q μ = Q μ := fun μ ↦ by
    simp only [Q, Matrix.diagonal_mul_diagonal, mul_ite, mul_one, mul_zero]
    congr 1
    funext i
    split_ifs <;> rfl
  have hidem : ∀ μ, (Q μ * P) * (Q μ * P) = Q μ * P := fun μ ↦ by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, ← hQ μ, Matrix.mul_assoc, hP, ← Matrix.mul_assoc,
      hQQ]
  refine ⟨∑ μ ∈ Finset.univ.image w,
    μ * (Module.finrank L (LinearMap.range (Matrix.toLin' (Q μ * P))) : K), ?_⟩
  simp only [map_sum, map_mul, map_natCast, ← pairQ_trace_idem_eq_finrank _ (hidem _)]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Q]
  rw [← Finset.sum_fiberwise_of_maps_to (g := w) (t := Finset.univ.image w)
    fun i _ ↦ Finset.mem_image_of_mem w (Finset.mem_univ i)]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  split_ifs with h
  · rw [h, one_mul]
  · rw [zero_mul, mul_zero]

/-- The coordinate blocks of a diagonal commuting with `A` commute with the spectral
projectors of `A`. -/
private theorem pairQ_diagonal_commute_specProj {K L ι : Type*} [Field K] [Field L] [Fintype ι]
    [DecidableEq ι] [DecidableEq K] (φ : K →+* L) (w : ι → K) (A : Matrix ι ι K)
    (hcomm : Matrix.diagonal w * A = A * Matrix.diagonal w) (r : ℕ) (η : L) (j : ℕ) (μ : K) :
    Matrix.diagonal (fun i ↦ if w i = μ then (1 : L) else 0) * pairQSpecProj (A.map φ) r η j =
      pairQSpecProj (A.map φ) r η j * Matrix.diagonal (fun i ↦ if w i = μ then (1 : L) else 0) := by
  have hB : Commute (Matrix.diagonal (fun i ↦ if w i = μ then (1 : L) else 0)) (A.map φ) := by
    ext i l
    have h := congrFun (congrFun hcomm i) l
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply]
    by_cases hA : A i l = 0
    · rw [hA, map_zero, mul_zero, zero_mul]
    · have hw : w i = w l := mul_right_cancel₀ hA (h.trans (mul_comm _ _))
      rw [hw, mul_comm]
  exact (((Commute.sum_right _ _ _ fun k _ ↦ (hB.pow_right k).smul_right _)).smul_right _).eq

/-- The weighted trace of a power of a matrix of finite order is invariant under exponents coprime
to the order, when the cyclotomic polynomials of the divisors of the order are irreducible. -/
theorem pairQ_trace_diagonal_mul_pow_eq {K : Type*} [Field K] [CharZero K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (w : ι → K) (A : Matrix ι ι K)
    (hcomm : Matrix.diagonal w * A = A * Matrix.diagonal w) {r s : ℕ} (hr : 0 < r)
    (hA : A ^ r = 1) (hs : Nat.Coprime s r)
    (hcyc : ∀ d : ℕ, d ∣ r → Irreducible (cyclotomic d K)) :
    (Matrix.diagonal w * A ^ s).trace = (Matrix.diagonal w * A).trace := by
  classical
  have : NeZero r := ⟨hr.ne'⟩
  set L := CyclotomicField r K
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta r K L) r :=
    IsCyclotomicExtension.zeta_spec r K L
  set ζ := IsCyclotomicExtension.zeta r K L
  set η := ζ⁻¹
  have hη : IsPrimitiveRoot η r := hζ.inv
  have hζη : ζ * η = 1 := mul_inv_cancel₀ (hζ.ne_zero hr.ne')
  set φ := algebraMap K L
  set B := A.map φ
  have hB : B ^ r = 1 := by
    rw [← Matrix.map_pow, hA, Matrix.map_one _ (map_zero φ) (map_one φ)]
  set W := Matrix.diagonal (fun i ↦ φ (w i))
  have hf : ∀ k, φ (Matrix.diagonal w * A ^ k).trace = (W * B ^ k).trace := fun k ↦ by
    rw [Matrix.trace, Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Matrix.diag_apply, Matrix.diagonal_mul, W, B, ← Matrix.map_pow, Matrix.map_apply,
      map_mul]
  set c : ℕ → L := fun j ↦ (W * pairQSpecProj B r η j).trace
  have hc : ∀ j, c j = (r : L)⁻¹ * ∑ k ∈ Finset.range r,
      η ^ (j * k) * φ (Matrix.diagonal w * A ^ k).trace := fun j ↦ by
    simp only [c, pairQ_trace_mul_specProj, hf]
  have hcK : ∀ j, ∃ x : K, c j = φ x := fun j ↦
    pairQ_trace_diagonal_mul_idem_mem φ w _ (pairQSpecProj_idem B r hr ζ η hB hη.pow_eq_one hζη j)
      (pairQ_diagonal_commute_specProj φ w A hcomm r η j)
  set σ := (IsCyclotomicExtension.autEquivPow L (hcyc r dvd_rfl)).symm
    (ZMod.unitOfCoprime s hs)
  have hσ : ∀ x : L, x ^ r = 1 → σ x = x ^ (s % r) := fun x hx ↦ by
    rw [IsCyclotomicExtension.autEquivPow_apply_of_pow_eq_one L (hcyc r dvd_rfl) σ hx,
      MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  have hmod : ∀ (x : L), x ^ r = 1 → ∀ n, x ^ n = x ^ (n % r) := fun x hx n ↦ by
    conv_lhs => rw [← Nat.div_add_mod n r, pow_add, pow_mul, hx, one_pow, one_mul]
  have hcs : ∀ j, c (s % r * j) = c j := fun j ↦ by
    obtain ⟨x, hx⟩ := hcK j
    have h1 : σ (c j) = c j := by rw [hx]; exact σ.commutes x
    rw [← h1, hc, hc, map_mul, map_inv₀, map_natCast, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_mul, map_pow, hσ η hη.pow_eq_one, ← pow_mul, AlgEquiv.commutes, ← mul_assoc]
  have hcm : ∀ j, c j = c (j % r) := fun j ↦ by
    rw [hc, hc]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [pow_mul, pow_mul, hmod η hη.pow_eq_one j]
  apply φ.injective
  conv_rhs => rw [← pow_one A]
  rw [hf, hf, pairQ_trace_mul_pow_eq_sum B W r hr ζ η hB hη hζη,
    pairQ_trace_mul_pow_eq_sum B W r hr ζ η hB hη hζη]
  simp only [mul_one]
  rw [← pairQ_sum_range_mul_mod (fun j ↦ ζ ^ j * c j) r (s % r) (by
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]; exact hs)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← hcm, mul_comm j (s % r), hcs, hmod ζ hζ.pow_eq_one (j * s), Nat.mod_mul_mod, mul_comm s j]

/-- The cyclotomic polynomials are irreducible over `ℚ(t)`. -/
theorem pairQ_irreducible_cyclotomic_ratFunc {d : ℕ} (hd : 0 < d) :
    Irreducible (cyclotomic d (RatFunc ℚ)) := by
  have hmon : (cyclotomic d ℚ[X]).Monic := cyclotomic.monic d _
  have hirr : Irreducible (cyclotomic d ℚ[X]) := by
    refine hmon.irreducible_of_irreducible_map (Polynomial.evalRingHom 0) _ ?_
    rw [map_cyclotomic]
    exact cyclotomic.irreducible_rat hd
  have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := RatFunc ℚ)).mp hirr
  rwa [map_cyclotomic] at h

end AJConjecture
