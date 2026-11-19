import Mathlib
import AJFamily.Quantum.TwistParamK

/-!
# Degree of the twist parameter

`[ℂ(z) : ℂ(K)] = 2m` for `K = twistParamK m = (z A B - 1)/(A B)`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- `U_n(X)` is monic of degree `n`. -/
private theorem chebU_X_natDegree_monic (n : ℕ) :
    (chebU (X : ℂ[X]) n).natDegree = n ∧ (chebU (X : ℂ[X]) n).Monic := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [chebU]
    | 1, _ => simp [chebU]
    | k + 2, ih =>
      obtain ⟨h1d, h1m⟩ := ih (k + 1) (by omega)
      obtain ⟨h0d, -⟩ := ih k (by omega)
      have hXm : (X * chebU (X : ℂ[X]) (k + 1)).Monic := monic_X.mul h1m
      have hXd : (X * chebU (X : ℂ[X]) (k + 1)).natDegree = k + 2 := by
        rw [natDegree_X_mul h1m.ne_zero, h1d]
      have hlt : (chebU (X : ℂ[X]) k).natDegree < (X * chebU (X : ℂ[X]) (k + 1)).natDegree := by
        rw [hXd, h0d]; omega
      rw [chebU]
      refine ⟨by rw [natDegree_sub_eq_left_of_natDegree_lt hlt, hXd], ?_⟩
      exact hXm.sub_of_left (degree_lt_degree hlt)

/-- For coprime `p, q` with `q ≠ 0`, the numerator and denominator of `p / q` have the degrees
of `p` and `q`. -/
private theorem natDegree_num_denom_div_of_isCoprime {p q : ℂ[X]} (hq : q ≠ 0)
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

theorem finrank_twistParamK (m : ℕ) (hm : 1 ≤ m) :
    Module.finrank ℂ⟮twistParamK m⟯ (RatFunc ℂ) = 2 * m := by
  set A : ℂ[X] := chebU (X : ℂ[X]) (m - 1) - chebU (X : ℂ[X]) m with hA
  set B : ℂ[X] := chebU (X : ℂ[X]) (m - 1) with hB
  obtain ⟨hBd, hBm⟩ := chebU_X_natDegree_monic (m - 1)
  obtain ⟨hmd, -⟩ := chebU_X_natDegree_monic m
  have hAd : A.natDegree = m := by
    rw [hA, natDegree_sub_eq_right_of_natDegree_lt (by rw [hBd, hmd]; omega), hmd]
  have hA0 : A ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hAd; omega
  have hP0 : A * B ≠ 0 := mul_ne_zero hA0 hBm.ne_zero
  have hPd : (A * B).natDegree = 2 * m - 1 := by
    rw [natDegree_mul hA0 hBm.ne_zero, hAd, hBd]; omega
  have hXPd : (X * (A * B)).natDegree = 2 * m := by
    rw [natDegree_X_mul hP0, hPd]; omega
  have hNd : (X * (A * B) - 1).natDegree = 2 * m := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [hXPd, natDegree_one]; omega), hXPd]
  have hcop : IsCoprime (X * (A * B) - 1) (A * B) := ⟨-1, X, by ring⟩
  have hK : twistParamK m = algebraMap ℂ[X] (RatFunc ℂ) (X * (A * B) - 1) /
      algebraMap ℂ[X] (RatFunc ℂ) (A * B) := by
    have h0 : algebraMap ℂ[X] (RatFunc ℂ) (A * B) ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℂ)).mpr hP0
    rw [twistParamK, ← hA, ← hB, ← RatFunc.algebraMap_X]
    field_simp
    simp only [map_sub, map_mul, map_one]
  obtain ⟨hn, hd⟩ := natDegree_num_denom_div_of_isCoprime hP0 hcop
  rw [RatFunc.finrank_eq_max_natDegree, hK, hn, hd, hNd, hPd]
  omega

end AJConjecture
