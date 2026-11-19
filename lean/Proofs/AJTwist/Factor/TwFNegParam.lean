import Mathlib
import AJTwist.Factor.TwFNegEval

/-!
# The rational parametrization of `T_(-b) = 0` (TwF, unit F2)

Source: revision 5, Section 5.1 (`operators.tex`, "Irreducibility of the residual blocks"): "For
`a = -b < 0` take instead `B = 𝒰_(b-1)`, `D = 𝒰_(b-2)`, `A = B - D`. Then `T_(-b) = A - e B` …
The adjacent identity again gives `e = A/B`, `J = 1 + (z - 2) B/A`, `K = z - 1/(A B)`. The same
exclusions hold, now with `A(2) = 1`. The rational function `K = (z A B - 1)/(A B)` has degree
`2b - 1` since the numerator and denominator are coprime of degrees `2b - 1`, `2b - 2`."

* `twistParamNegK b = z - 1/(A(z) B(z)) ∈ ℂ(z)`, with `B = V_b = U_(b-1)`,
  `A = V_b - V_(b-1) = U_(b-1) - U_(b-2)`.
* `famParamNeg_inverse`: on `T_(-b)(K, J) = 0`, with `Z = 1 + K - K J + J²`:
  `B(Z) ≠ 0`, `A(Z) ≠ 0` and `K = Z - 1/(A(Z) B(Z))` (over every field).
* `finrank_twistParamNegK`: `[ℂ(z) : ℂ(K(z))] = 2b - 1`.

Route: `famParam_inverse` (`AJFamily/Quantum/TwistParam.lean`) and `finrank_twistParamK`
(`TwistParamDegree.lean`) with `(U_(m-1) - U_m, U_(m-1)) → (V_b - V_(b-1), V_b)`: the Chebyshev
identity `V_(n+1)² + V_n² - z V_(n+1) V_n = 1` (`chebU_succ_sq_add` through `twfChebV_succ`),
`T_(-b) = 0 ⟺ (K - J) B = D`; `z A B - 1` and `A B` are coprime (trivially) of degrees `2b - 1`
and `2b - 2` (`V_n(X)` is monic of degree `n - 1`), and the degree of `ℂ(z)` over `ℂ(f)` is the
larger of the degrees of numerator and denominator (as in `finrank_twistParamK`). Unlike the
positive case, no root computation is needed for coprimality.
Checked symbolically for `b ≤ 5` (scratch `check_blocks.py`).
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- The rational function `K(z) = z - 1/(A(z) B(z))`, `B = V_b`, `A = V_b - V_(b-1)`. -/
def twistParamNegK (b : ℕ) : RatFunc ℂ :=
  RatFunc.X - (algebraMap ℂ[X] (RatFunc ℂ)
    ((twfChebV (X : ℂ[X]) b - twfChebV (X : ℂ[X]) (b - 1)) * twfChebV (X : ℂ[X]) b))⁻¹

/-- `V_(n+1)² + V_n² - z V_(n+1) V_n = 1`. -/
private theorem twfChebV_succ_sq_add_twfNegParam {R : Type*} [CommRing R] (z : R) (n : ℕ) :
    twfChebV z (n + 1) ^ 2 + twfChebV z n ^ 2 - z * twfChebV z (n + 1) * twfChebV z n = 1 := by
  induction n with
  | zero => simp [twfChebV]
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 from rfl, twfChebV]
    linear_combination ih

/-- On the curve `T_(-b)(K, J) = 0` the meridian trace is `K = Z - 1/(A(Z) B(Z))`. -/
theorem famParamNeg_inverse {F : Type*} [Field F] {b : ℕ} (hb : 1 ≤ b) {K J : F}
    (hT : famTKNeg b K J = 0) :
    twfChebV (famZK K J) b ≠ 0 ∧ twfChebV (famZK K J) b - twfChebV (famZK K J) (b - 1) ≠ 0 ∧
      K = famZK K J - ((twfChebV (famZK K J) b - twfChebV (famZK K J) (b - 1)) *
        twfChebV (famZK K J) b)⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  have hc := twfChebV_succ_sq_add_twfNegParam (famZK K J) n
  unfold famTKNeg at hT
  rw [Nat.add_sub_cancel] at hT ⊢
  set Z := famZK K J with hZ
  set B := twfChebV Z (n + 1)
  set D := twfChebV Z n
  have hD : D = (K - J) * B := by linear_combination -hT
  have hZ' : Z = 1 + K - K * J + J ^ 2 := hZ
  have hcas : B ^ 2 * ((Z - K) * (1 + J - K)) = 1 := by
    rw [hD] at hc
    linear_combination hc + B ^ 2 * hZ'
  have hB : B ≠ 0 := by
    rintro h
    rw [h] at hcas
    simp at hcas
  have he : 1 + J - K ≠ 0 := by
    rintro h
    rw [h] at hcas
    simp at hcas
  have hA : B - D = B * (1 + J - K) := by rw [hD]; ring
  refine ⟨hB, by rw [hA]; exact mul_ne_zero hB he, ?_⟩
  rw [hA]
  field_simp
  linear_combination -hcas

/-- `V_(n+1)(X)` is monic of degree `n`. -/
private theorem twfChebV_X_natDegree_monic_twfNegParam (n : ℕ) :
    (twfChebV (X : ℂ[X]) (n + 1)).natDegree = n ∧ (twfChebV (X : ℂ[X]) (n + 1)).Monic := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [twfChebV]
    | 1, _ => simp [twfChebV]
    | k + 2, ih =>
      obtain ⟨h1d, h1m⟩ := ih (k + 1) (by omega)
      obtain ⟨h0d, -⟩ := ih k (by omega)
      have hXm : (X * twfChebV (X : ℂ[X]) (k + 2)).Monic := monic_X.mul h1m
      have hXd : (X * twfChebV (X : ℂ[X]) (k + 2)).natDegree = k + 2 := by
        rw [natDegree_X_mul h1m.ne_zero, h1d]
      have hlt : (twfChebV (X : ℂ[X]) (k + 1)).natDegree <
          (X * twfChebV (X : ℂ[X]) (k + 2)).natDegree := by
        rw [hXd, h0d]; omega
      rw [show k + 2 + 1 = (k + 1) + 2 from rfl, twfChebV]
      refine ⟨by rw [natDegree_sub_eq_left_of_natDegree_lt hlt, hXd], ?_⟩
      exact hXm.sub_of_left (degree_lt_degree hlt)

/-- For coprime `p, q` with `q ≠ 0`, the numerator and denominator of `p / q` have the degrees
of `p` and `q`. -/
private theorem natDegree_num_denom_div_of_isCoprime_twfNegParam {p q : ℂ[X]} (hq : q ≠ 0)
    (hpq : IsCoprime p q) :
    (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q).num.natDegree =
        p.natDegree ∧
      (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q).denom.natDegree =
        q.natDegree := by
  set x : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q with hx
  have h : x.num * q = p * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr hx
  have hnd : IsCoprime x.num x.denom := x.isCoprime_num_denom
  have h1 : p ∣ x.num := hpq.dvd_of_dvd_mul_right (Dvd.intro x.denom h.symm)
  have h2 : x.num ∣ p := hnd.dvd_of_dvd_mul_right (Dvd.intro q h)
  have h3 : q ∣ x.denom := hpq.symm.dvd_of_dvd_mul_left (Dvd.intro_left x.num h)
  have h4 : x.denom ∣ q := hnd.symm.dvd_of_dvd_mul_left (Dvd.intro_left p h.symm)
  exact ⟨natDegree_eq_of_degree_eq <|
      degree_eq_degree_of_associated (associated_of_dvd_dvd h2 h1),
    natDegree_eq_of_degree_eq <| degree_eq_degree_of_associated (associated_of_dvd_dvd h4 h3)⟩

/-- `A = V_b - V_(b-1)` is nonzero of degree `b - 1` (`b ≥ 1`). -/
private theorem natDegree_twfChebV_sub_twfNegParam (b : ℕ) (hb : 1 ≤ b) :
    (twfChebV (X : ℂ[X]) b - twfChebV (X : ℂ[X]) (b - 1)).natDegree = b - 1 ∧
      twfChebV (X : ℂ[X]) b - twfChebV (X : ℂ[X]) (b - 1) ≠ 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  obtain ⟨hd, hm⟩ := twfChebV_X_natDegree_monic_twfNegParam n
  rcases n with _ | k
  · simp [twfChebV]
  · obtain ⟨hd', -⟩ := twfChebV_X_natDegree_monic_twfNegParam k
    have hlt : (twfChebV (X : ℂ[X]) (k + 1)).natDegree <
        (twfChebV (X : ℂ[X]) (k + 1 + 1)).natDegree := by rw [hd, hd']; omega
    have hdeg := natDegree_sub_eq_left_of_natDegree_lt hlt
    refine ⟨by rw [hdeg, hd], fun h ↦ ?_⟩
    rw [h, natDegree_zero, hd] at hdeg
    omega

/-- `ℂ(z)` has degree `2b - 1` over `ℂ(K(z))`. -/
theorem finrank_twistParamNegK (b : ℕ) (hb : 1 ≤ b) :
    Module.finrank ℂ⟮twistParamNegK b⟯ (RatFunc ℂ) = 2 * b - 1 := by
  set A : ℂ[X] := twfChebV (X : ℂ[X]) b - twfChebV (X : ℂ[X]) (b - 1) with hA
  set B : ℂ[X] := twfChebV (X : ℂ[X]) b with hB
  obtain ⟨hAd, hA0⟩ := natDegree_twfChebV_sub_twfNegParam b hb
  obtain ⟨hBd, hBm⟩ : B.natDegree = b - 1 ∧ B.Monic := by
    have h := twfChebV_X_natDegree_monic_twfNegParam (b - 1)
    rwa [Nat.sub_add_cancel hb] at h
  have hP0 : A * B ≠ 0 := mul_ne_zero hA0 hBm.ne_zero
  have hPd : (A * B).natDegree = 2 * b - 2 := by
    rw [natDegree_mul hA0 hBm.ne_zero, hAd, hBd]; omega
  have hXPd : (X * (A * B)).natDegree = 2 * b - 1 := by
    rw [natDegree_X_mul hP0, hPd]; omega
  have hNd : (X * (A * B) - 1).natDegree = 2 * b - 1 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [hXPd, natDegree_one]; omega), hXPd]
  have hcop : IsCoprime (X * (A * B) - 1) (A * B) := ⟨-1, X, by ring⟩
  have hK : twistParamNegK b = algebraMap ℂ[X] (RatFunc ℂ) (X * (A * B) - 1) /
      algebraMap ℂ[X] (RatFunc ℂ) (A * B) := by
    have h0 : algebraMap ℂ[X] (RatFunc ℂ) (A * B) ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr hP0
    rw [twistParamNegK, ← hA, ← hB, ← RatFunc.algebraMap_X]
    field_simp
    simp only [map_sub, map_mul, map_one]
  obtain ⟨hn, hd⟩ := natDegree_num_denom_div_of_isCoprime_twfNegParam hP0 hcop
  rw [RatFunc.finrank_eq_max_natDegree, hK, hn, hd, hNd, hPd]
  omega

end AJConjecture
