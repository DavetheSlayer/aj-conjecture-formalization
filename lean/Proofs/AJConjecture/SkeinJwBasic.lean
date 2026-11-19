import Mathlib
import AJConjecture.ClaspAlgBasic
import AJConjecture.SkeinJonesWenzl
import AJConjecture.SkeinTlRelations

/-!
# The Jones–Wenzl projector is an idempotent killed by the generators

Induction on `k` with Wenzl's recursion (Kauffman–Lins, Ch. 3; Lickorish, Ch. 13):
`f_k² = f_k` and `e_j f_k = f_k e_j = 0` for the generators inside the block. The induction also
needs `f_{k+1} e_{i+k} f_{k+1} e_{i+k} f_{k+1} = -([k+2]/[k+1]) f_{k+1} e_{i+k} f_{k+1}`. The
statements hold for every ambient size, because the recursion is stationary once `e_{i+k} = 0`.
-/

namespace AJConjecture

/-- The three-term recursion of the quantum integers: `[2] [m] = [m+1] + [m-1]`. -/
theorem quantumInt_recurrence (m : ℤ) :
    ((RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) + RatFunc.X ^ (-2 : ℤ)) * quantumInt m =
      quantumInt (m + 1) + quantumInt (m - 1) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  simp only [quantumInt]
  rw [← add_div, ← mul_div_assoc]
  congr 1
  rw [show 2 * (m + 1) = 2 * m + 2 from by ring, show -(2 * m + 2) = -(2 * m) + -2 from by ring,
    show 2 * (m - 1) = 2 * m + -2 from by ring, show -(2 * m + -2) = -(2 * m) + 2 from by ring,
    zpow_add₀ hX, zpow_add₀ hX, zpow_add₀ hX, zpow_add₀ hX]
  ring

/-- The scalar identity behind Wenzl's recursion:
`([k+1]/[k+2]) (δ + [k]/[k+1]) = -1`. -/
theorem wenzl_scalar (k : ℕ) :
    quantumInt ((k : ℤ) + 1) / quantumInt ((k : ℤ) + 2) *
      ((-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) +
        quantumInt (k : ℤ) / quantumInt ((k : ℤ) + 1)) = -1 := by
  have h1 : quantumInt ((k : ℤ) + 1) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have h2 : quantumInt ((k : ℤ) + 2) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
  have hrec := quantumInt_recurrence ((k : ℤ) + 1)
  rw [show (k : ℤ) + 1 + 1 = (k : ℤ) + 2 from by ring, show (k : ℤ) + 1 - 1 = (k : ℤ) from by ring]
    at hrec
  rw [div_mul_eq_mul_div, div_eq_iff h2, mul_add, mul_div_cancel₀ _ h1]
  linear_combination -hrec

/-- The algebra of one step of Wenzl's recursion: if `f` is an idempotent absorbing `g`, `g`
commutes with `e` and `e f e = d g e` with `c d = -1`, then `f + c f e f` is an idempotent killed
by `e` on both sides. -/
private theorem wenzl_step_jwBasic {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (f g e : A) (c d : K) (hff : f * f = f) (hfg : f * g = f) (hgf : g * f = f)
    (hge : g * e = e * g) (hefe : e * f * e = d • (g * e)) (hcd : c * d = -1) :
    (f + c • (f * e * f)) * (f + c • (f * e * f)) = f + c • (f * e * f) ∧
      e * (f + c • (f * e * f)) = 0 ∧ (f + c • (f * e * f)) * e = 0 := by
  have hff' : ∀ x : A, f * (f * x) = f * x := fun x ↦ by rw [← mul_assoc, hff]
  have hfg' : ∀ x : A, f * (g * x) = f * x := fun x ↦ by rw [← mul_assoc, hfg]
  have hefe' : ∀ x : A, e * (f * (e * x)) = d • (g * (e * x)) := fun x ↦ by
    rw [← mul_assoc, ← mul_assoc, hefe, smul_mul_assoc, mul_assoc]
  have hge' : ∀ x : A, g * (e * x) = e * (g * x) := fun x ↦ by
    rw [← mul_assoc, hge, mul_assoc]
  have hefe'' : e * (f * e) = d • (e * g) := by rw [← mul_assoc, hefe, hge]
  refine ⟨?_, ?_, ?_⟩
  · simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc, hff, hff', hefe',
      hfg', smul_smul]
    match_scalars <;> first | ring1 | linear_combination c * hcd
  · simp only [mul_add, mul_smul_comm, mul_assoc, hefe', hge', hgf, smul_smul, hcd]
    module
  · simp only [add_mul, smul_mul_assoc, mul_assoc, hefe'', hfg', mul_smul_comm,
      smul_smul, hcd, ← hge]
    module

/-- `f_k` commutes with the generators on the right of its block. -/
private theorem jwAt_commute_tlGenF_of_le_jwBasic (n i : ℕ) :
    ∀ k j : ℕ, i + k ≤ j → Commute (jwAt n i k) (tlGenF n j)
  | 0, _, _ => by rw [jwAt]; exact Commute.one_left _
  | 1, _, _ => by rw [jwAt]; exact Commute.one_left _
  | k + 2, j, h => by
    rw [jwAt]
    have h1 := jwAt_commute_tlGenF_of_le_jwBasic n i (k + 1) j (by omega)
    have h2 : Commute (tlGenF n (i + k)) (tlGenF n j) := tlGenF_commute n (i + k) j (by omega)
    exact h1.add_left (((h1.mul_left h2).mul_left h1).smul_left _)

/-- The algebra behind `e f e = (δ + c) g e` for `f = g + c g e' g`. -/
theorem wenzl_sandwich {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (g e e' : A) (c δ : K) (hgg : g * g = g) (hge : g * e = e * g) (hee : e * e = δ • e)
    (hrel : e * e' * e = e) :
    e * (g + c • (g * e' * g)) * e = (δ + c) • (g * e) := by
  have h1 : e * g * e = δ • (g * e) := by rw [← hge, mul_assoc, hee, mul_smul_comm]
  have h2 : e * (g * e' * g) * e = g * e :=
    calc e * (g * e' * g) * e = (e * g) * e' * (g * e) := by simp only [mul_assoc]
      _ = (g * e) * e' * (e * g) := by rw [hge]
      _ = g * (e * e' * e) * g := by simp only [mul_assoc]
      _ = g * e * g := by rw [hrel]
      _ = g * e := by rw [mul_assoc, ← hge, ← mul_assoc, hgg]
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, h1, h2, add_smul]

/-- `e_{i+k} f_{k+1} e_{i+k} = (δ + [k]/[k+1]) f_k e_{i+k}`, given that `f_k` is an
idempotent. -/
private theorem tlGenF_mul_jwAt_succ_mul_tlGenF_jwBasic (n i k : ℕ)
    (hg : jwAt n i k * jwAt n i k = jwAt n i k) :
    tlGenF n (i + k) * jwAt n i (k + 1) * tlGenF n (i + k) =
      ((-(RatFunc.X : RatFunc ℚ) ^ (2 : ℤ) - RatFunc.X ^ (-2 : ℤ)) +
        quantumInt (k : ℤ) / quantumInt ((k : ℤ) + 1)) • (jwAt n i k * tlGenF n (i + k)) := by
  cases k with
  | zero =>
    have h0 : quantumInt ((0 : ℕ) : ℤ) = 0 := by simp [quantumInt]
    simp only [jwAt, Matrix.mul_one, Matrix.one_mul, h0, zero_div, add_zero]
    exact tlGenF_mul_self n i
  | succ k =>
    rw [show jwAt n i (k + 1 + 1) = jwAt n i (k + 1) + (quantumInt ((k : ℤ) + 1) /
      quantumInt ((k : ℤ) + 2)) • (jwAt n i (k + 1) * tlGenF n (i + k) * jwAt n i (k + 1)) from by
        rw [jwAt], show (((k + 1 : ℕ) : ℤ)) = (k : ℤ) + 1 from by push_cast; ring,
      show (k : ℤ) + 1 + 1 = (k : ℤ) + 2 from by ring]
    exact wenzl_sandwich (jwAt n i (k + 1)) (tlGenF n (i + (k + 1))) (tlGenF n (i + k)) _ _
      hg (jwAt_commute_tlGenF_of_le_jwBasic n i (k + 1) (i + (k + 1)) le_rfl).eq
      (tlGenF_mul_self n _) (tlGenF_succ_mul_mul n (i + k))

/-- `f_{k+1} f_k = f_{k+1}` and `f_k f_{k+1} = f_{k+1}`, given that `f_k` is an idempotent. -/
private theorem jwAt_succ_absorb_jwBasic (n i k : ℕ)
    (hg : jwAt n i k * jwAt n i k = jwAt n i k) :
    jwAt n i (k + 1) * jwAt n i k = jwAt n i (k + 1) ∧
      jwAt n i k * jwAt n i (k + 1) = jwAt n i (k + 1) := by
  cases k with
  | zero => simp [jwAt]
  | succ k =>
    rw [show jwAt n i (k + 1 + 1) = jwAt n i (k + 1) + (quantumInt ((k : ℤ) + 1) /
      quantumInt ((k : ℤ) + 2)) • (jwAt n i (k + 1) * tlGenF n (i + k) * jwAt n i (k + 1)) from by
        rw [jwAt]]
    constructor
    · rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hg]
    · rw [Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]

/-- The Jones–Wenzl projector is an idempotent killed on both sides by the generators of its
block. -/
private theorem jwAt_idem_and_kill_jwBasic (n i : ℕ) :
    ∀ k : ℕ, jwAt n i k * jwAt n i k = jwAt n i k ∧
      ∀ j : ℕ, i ≤ j → j + 1 < i + k →
        tlGenF n j * jwAt n i k = 0 ∧ jwAt n i k * tlGenF n j = 0
  | 0 => ⟨by simp [jwAt], fun j _ _ ↦ by omega⟩
  | 1 => ⟨by simp [jwAt], fun j _ _ ↦ by omega⟩
  | k + 2 => by
    obtain ⟨hgg, -⟩ := jwAt_idem_and_kill_jwBasic n i k
    obtain ⟨hff, hkill⟩ := jwAt_idem_and_kill_jwBasic n i (k + 1)
    obtain ⟨hfg, hgf⟩ := jwAt_succ_absorb_jwBasic n i k hgg
    obtain ⟨hFF, heF, hFe⟩ := wenzl_step_jwBasic (jwAt n i (k + 1)) (jwAt n i k)
      (tlGenF n (i + k)) (quantumInt ((k : ℤ) + 1) / quantumInt ((k : ℤ) + 2)) _ hff hfg hgf
      (jwAt_commute_tlGenF_of_le_jwBasic n i k (i + k) le_rfl).eq
      (tlGenF_mul_jwAt_succ_mul_tlGenF_jwBasic n i k hgg) (wenzl_scalar k)
    rw [jwAt]
    refine ⟨hFF, fun j hij hjk ↦ ?_⟩
    rcases Nat.lt_or_ge (j + 1) (i + (k + 1)) with hlt | hge
    · obtain ⟨h1, h2⟩ := hkill j hij hlt
      constructor
      · rw [Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1,
          Matrix.zero_mul, Matrix.zero_mul, smul_zero, add_zero]
      · rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, h2, Matrix.mul_zero, smul_zero,
          add_zero]
    · obtain rfl : j = i + k := by omega
      exact ⟨heF, hFe⟩

/-- `f_k² = f_k`. -/
theorem jwAt_mul_self (n i k : ℕ) : jwAt n i k * jwAt n i k = jwAt n i k :=
  (jwAt_idem_and_kill_jwBasic n i k).1

/-- `e_j f_k = 0` for a generator inside the block of `f_k`. -/
theorem tlGenF_mul_jwAt (n i k j : ℕ) (hij : i ≤ j) (hjk : j + 1 < i + k) :
    tlGenF n j * jwAt n i k = 0 :=
  ((jwAt_idem_and_kill_jwBasic n i k).2 j hij hjk).1

/-- `f_k e_j = 0` for a generator inside the block of `f_k`. -/
theorem jwAt_mul_tlGenF (n i k j : ℕ) (hij : i ≤ j) (hjk : j + 1 < i + k) :
    jwAt n i k * tlGenF n j = 0 :=
  ((jwAt_idem_and_kill_jwBasic n i k).2 j hij hjk).2

end AJConjecture
