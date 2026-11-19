import Mathlib
import AJFamily.Quantum.BiquadraticIrreducible
import AJFamily.Quantum.TwistParam
import AJFamily.Quantum.TwistParamDegree
import AJFamily.Quantum.TwistParamNotSquare
import AJFamily.Quantum.TwistPolyBasic

/-!
# Irreducible factors of the twist polynomial

For `m ≥ 2`, every irreducible factor of `B_m` in `ℂ(M)[L]` has degree at least `2m`. At a root,
`K = M² + M⁻²` is the twist parameter `twistParamK m` of a transcendental `z`, and comparing
`[ℂ(z, M) : ℂ(K)] = 8m` with `[ℂ(M) : ℂ(K)] ≤ 4` gives the bound.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Ring homomorphisms commute with `chebU`. -/
private theorem chebU_map_ringHom_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (z : R) : ∀ n : ℕ, f (chebU z n) = chebU (f z) n
  | 0 => by simp [chebU]
  | 1 => by simp [chebU]
  | n + 2 => by
    rw [chebU, chebU, map_sub, map_mul, chebU_map_ringHom_eq f z (n + 1), chebU_map_ringHom_eq f z n]

/-- A `ℂ`-algebra map out of `RatFunc ℂ` sends a polynomial to its evaluation at the image
of `X`. -/
private theorem algHom_ratFunc_algebraMap {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (φ : RatFunc ℂ →ₐ[ℂ] Ω) (p : ℂ[X]) :
    φ (algebraMap ℂ[X] (RatFunc ℂ) p) = aeval (φ RatFunc.X) p := by
  have h : φ.comp (IsScalarTower.toAlgHom ℂ ℂ[X] (RatFunc ℂ)) = aeval (φ RatFunc.X) := by
    refine Polynomial.algHom_ext ?_
    simp [RatFunc.algebraMap_X]
  exact congrArg (fun ψ : ℂ[X] →ₐ[ℂ] Ω ↦ ψ p) h

/-- A polynomial evaluated at `y` lies in `ℂ⟮y⟯`. -/
private theorem aeval_mem_adjoin_simple_complex {Ω : Type*} [Field Ω] [Algebra ℂ Ω] (y : Ω)
    (p : ℂ[X]) : aeval y p ∈ ℂ⟮y⟯ := by
  have h := aeval_algebraMap_apply Ω (AdjoinSimple.gen ℂ y) p
  rw [AdjoinSimple.algebraMap_gen] at h
  rw [h]
  exact Subtype.mem _

/-- The image of a `ℂ`-algebra map out of `RatFunc ℂ` lies in `ℂ⟮φ X⟯`. -/
private theorem algHom_ratFunc_mem_adjoin {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (φ : RatFunc ℂ →ₐ[ℂ] Ω) (r : RatFunc ℂ) : φ r ∈ ℂ⟮φ RatFunc.X⟯ := by
  rw [← RatFunc.num_div_denom r, map_div₀, algHom_ratFunc_algebraMap,
    algHom_ratFunc_algebraMap]
  exact div_mem (aeval_mem_adjoin_simple_complex _ _) (aeval_mem_adjoin_simple_complex _ _)

/-- Evaluating the image of `twistPoly k` in `ℂ(M)[L]` at a point `L` of a `ℂ(M)`-algebra `Ω`
is the bivariate evaluation at `(M, L)`. -/
private theorem aeval_map_twistPoly_eq_evalEval {Ω : Type*} [Field Ω] [Algebra (RatFunc ℂ) Ω]
    (k : ℕ) (L : Ω) :
    aeval L ((twistPoly k).map
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))) =
    ((twistPoly k).map (Polynomial.mapRingHom (Int.castRingHom Ω))).evalEval
      (algebraMap (RatFunc ℂ) Ω RatFunc.X) L := by
  set M := algebraMap (RatFunc ℂ) Ω RatFunc.X
  have hhom : (algebraMap (RatFunc ℂ) Ω).comp
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ))) =
      (evalRingHom M).comp (Polynomial.mapRingHom (Int.castRingHom Ω)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp
    · simp [M, RatFunc.algebraMap_X]
  have hrhs : ((twistPoly k).map (Polynomial.mapRingHom (Int.castRingHom Ω))).evalEval M L =
      (twistPoly k).eval₂ ((evalRingHom M).comp (Polynomial.mapRingHom (Int.castRingHom Ω))) L := by
    rw [evalEval, ← coe_evalRingHom, eval, hom_eval₂, eval₂_map]
    simp
  rw [hrhs, aeval_def, eval₂_map, hhom]

/-- At a root `L` of `B_k` in a field `Ω` over `ℂ(M)`, `L + M² ≠ 0`, because
`B_k(M, -M²) = M^(2k) (1 - M⁴)^(2k) ≠ 0`. -/
private theorem root_add_sq_ne_zero_of_twistPoly {Ω : Type*} [Field Ω]
    [Algebra (RatFunc ℂ) Ω] (k : ℕ) {L : Ω} (hL : aeval L ((twistPoly k).map
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))) = 0) :
    L + (algebraMap (RatFunc ℂ) Ω RatFunc.X) ^ 2 ≠ 0 := by
  set ψ : ℤ[X] →+* Ω := (algebraMap (RatFunc ℂ) Ω).comp
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ))) with hψ
  have hinj : Function.Injective ψ := by
    refine (algebraMap (RatFunc ℂ) Ω).injective.comp ((RatFunc.algebraMap_injective ℂ).comp ?_)
    exact Polynomial.map_injective _ (Int.castRingHom ℂ).injective_int
  intro h
  have hLx : L = ψ (-(X ^ 2)) := by
    simp only [ψ, RingHom.comp_apply, map_neg, map_pow, coe_mapRingHom, Polynomial.map_X,
      RatFunc.algebraMap_X]
    linear_combination h
  rw [aeval_def, eval₂_map, ← hψ, hLx, eval₂_at_apply, eval_neg_twistPoly] at hL
  have h0 := hinj (hL.trans (map_zero ψ).symm)
  have h1 : (1 - X ^ 4 : ℤ[X]) ≠ 0 := fun h ↦ by simpa using congrArg (eval 0) h
  exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ h1) h0

/-- At a root `L` of `B_k` in a field `Ω` over `ℂ(M)`, `T_k(Z, e) = 0` for
`K = x + 1/x`, `J = (xL + 1)/(L + x)`, `x = M²`. -/
private theorem famTK_eq_zero_of_twistPoly_root {Ω : Type*} [Field Ω]
    [Algebra (RatFunc ℂ) Ω] {k : ℕ} (hk : 1 ≤ k) {L : Ω} (hL : aeval L ((twistPoly k).map
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))) = 0) :
    famTK k (famKQ ((algebraMap (RatFunc ℂ) Ω RatFunc.X) ^ 2))
      (((algebraMap (RatFunc ℂ) Ω RatFunc.X) ^ 2 * L + 1) /
        (L + (algebraMap (RatFunc ℂ) Ω RatFunc.X) ^ 2)) = 0 := by
  have hM : algebraMap (RatFunc ℂ) Ω RatFunc.X ≠ 0 := by
    simp [RatFunc.X_ne_zero]
  have hL' := root_add_sq_ne_zero_of_twistPoly k hL
  rw [aeval_map_twistPoly_eq_evalEval, evalEval_twistPoly hM hL' hk] at hL
  exact (mul_eq_zero.mp hL).resolve_left
    (mul_ne_zero (pow_ne_zero _ hL') (pow_ne_zero _ (pow_ne_zero _ hM)))

/-- If `M⁴ - K M² + 1 = 0`, `K = z - ((U_(m-1)(z) - U_m(z)) U_(m-1)(z))⁻¹` and `M` is
transcendental over `ℂ`, then so is `z`: otherwise `z`, hence `K`, hence `M` would lie in `ℂ`. -/
private theorem transcendental_of_twistParam_eq {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {m : ℕ}
    {M K z : Ω} (hM : Transcendental ℂ M) (hM4 : M ^ 4 - K * M ^ 2 + 1 = 0)
    (hK : K = z - ((chebU z (m - 1) - chebU z m) * chebU z (m - 1))⁻¹) :
    Transcendental ℂ z := by
  intro hz
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one ℂ z
    (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hz.isIntegral))
  set k : ℂ := c - ((chebU c (m - 1) - chebU c m) * chebU c (m - 1))⁻¹
  have hk : K = algebraMap ℂ Ω k := by
    rw [hK, ← hc]
    simp only [k, map_sub, map_mul, map_inv₀, chebU_map_ringHom_eq]
  refine hM ⟨X ^ 4 - C k * X ^ 2 + 1, ?_, ?_⟩
  · have : (X ^ 4 - C k * X ^ 2 + 1 : ℂ[X]).natDegree = 4 := by compute_degree!
    intro h
    rw [h, natDegree_zero] at this
    exact absurd this (by norm_num)
  · simp [← hk, hM4]

/-- The relative degree of `A ⊔ ℂ⟮y⟯` over `A` is the degree of `A⟮y⟯` over `A`. -/
private theorem relfinrank_sup_adjoin_simple {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (A : IntermediateField ℂ Ω) (y : Ω) :
    relfinrank A (A ⊔ ℂ⟮y⟯) = Module.finrank A A⟮y⟯ := by
  rw [relfinrank_eq_finrank_of_le le_sup_left]
  have h : extendScalars (le_sup_left : A ≤ A ⊔ ℂ⟮y⟯) = A⟮y⟯ := restrictScalars_injective ℂ <| by
    rw [extendScalars_restrictScalars, restrictScalars_adjoin_eq_sup]
  rw [h]

/-- The `ℂ`-algebra map `RatFunc ℂ → Ω`, `X ↦ z`, sends `twistParamK m` to
`z - ((U_(m-1)(z) - U_m(z)) U_(m-1)(z))⁻¹`. -/
private theorem algHom_ratFunc_twistParamK {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (φ : RatFunc ℂ →ₐ[ℂ] Ω) (m : ℕ) :
    φ (twistParamK m) = φ RatFunc.X - ((chebU (φ RatFunc.X) (m - 1) - chebU (φ RatFunc.X) m) *
      chebU (φ RatFunc.X) (m - 1))⁻¹ := by
  have hU : ∀ n : ℕ, aeval (φ RatFunc.X) (chebU (X : ℂ[X]) n) = chebU (φ RatFunc.X) n := by
    intro n
    have h := chebU_map_ringHom_eq (aeval (φ RatFunc.X)).toRingHom (X : ℂ[X]) n
    simpa using h
  rw [twistParamK, map_sub, map_inv₀, algHom_ratFunc_algebraMap, map_mul, map_sub, hU, hU]

/-- `[ℂ(z) : ℂ(K)] = 2m` for transcendental `z` and `K = K(z)`. -/
private theorem relfinrank_adjoin_twistParamK {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {m : ℕ}
    (hm : 1 ≤ m) {K z : Ω} (hz : Transcendental ℂ z)
    (hK : K = z - ((chebU z (m - 1) - chebU z m) * chebU z (m - 1))⁻¹) :
    relfinrank ℂ⟮K⟯ ℂ⟮z⟯ = 2 * m := by
  set f : RatFunc ℂ →ₐ[ℂ] Ω := ℂ⟮z⟯.val.comp (RatFunc.algEquivOfTranscendental z hz).toAlgHom
  have hfX : f RatFunc.X = z := by simp [f]
  have hfK : f (twistParamK m) = K := by rw [algHom_ratFunc_twistParamK, hfX, hK]
  have h1 : ℂ⟮K⟯ = (ℂ⟮twistParamK m⟯).map f := by rw [adjoin_map, Set.image_singleton, hfK]
  have h2 : ℂ⟮z⟯ = (⊤ : IntermediateField ℂ (RatFunc ℂ)).map f := by
    rw [← AlgHom.fieldRange_eq_map]
    refine le_antisymm (adjoin_simple_le_iff.mpr ⟨RatFunc.X, hfX⟩) ?_
    rintro _ ⟨r, rfl⟩
    exact ((RatFunc.algEquivOfTranscendental z hz) r).2
  rw [h1, h2, relfinrank_map_map, relfinrank_top_right, finrank_twistParamK m hm]

/-- `[ℂ(z, M) : ℂ(z)] = 4`, since `X⁴ - K(z) X² + 1` is irreducible over `ℂ(z)`. -/
private theorem relfinrank_sup_adjoin_biquadratic {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {m : ℕ}
    (hm : 2 ≤ m) {M K z : Ω} (hz : Transcendental ℂ z) (hM4 : M ^ 4 - K * M ^ 2 + 1 = 0)
    (hK : K = z - ((chebU z (m - 1) - chebU z m) * chebU z (m - 1))⁻¹) :
    relfinrank ℂ⟮z⟯ (ℂ⟮z⟯ ⊔ ℂ⟮M⟯) = 4 := by
  set e := RatFunc.algEquivOfTranscendental z hz
  set a : ℂ⟮z⟯ := e (twistParamK m)
  have ha : (a : Ω) = K :=
    (algHom_ratFunc_twistParamK (ℂ⟮z⟯.val.comp e.toAlgHom) m).trans (by simp [e, hK])
  have hsq : ∀ b : RatFunc ℂ, ¬ IsSquare b → ¬ IsSquare (e b) := fun b hb h ↦
    hb (by simpa using h.map e.symm)
  obtain ⟨n1, n2, n3⟩ := not_isSquare_twistParamK m hm
  have h2 : (2 : ℂ⟮z⟯) ≠ 0 := by
    rw [← map_ofNat e 2]
    exact (map_ne_zero_iff _ e.injective).mpr two_ne_zero
  have hirr : Irreducible (X ^ 4 - C a * X ^ 2 + 1 : ℂ⟮z⟯[X]) := by
    refine irreducible_X_pow_four_sub_C_mul_add_one h2 ?_ ?_ ?_
    · simpa [a, map_add, map_ofNat] using hsq _ n1
    · simpa [a, map_sub, map_ofNat] using hsq _ n2
    · simpa [a, map_mul, map_add, map_sub, map_ofNat] using hsq _ n3
  have hmon : (X ^ 4 - C a * X ^ 2 + 1 : ℂ⟮z⟯[X]).Monic := by monicity!
  have hev : aeval M (X ^ 4 - C a * X ^ 2 + 1 : ℂ⟮z⟯[X]) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one,
      IntermediateField.algebraMap_apply, ha]
    exact hM4
  rw [relfinrank_sup_adjoin_simple, adjoin.finrank ⟨_, hmon, hev⟩,
    ← minpoly.eq_of_irreducible_of_monic hirr hev hmon]
  compute_degree!

/-- `chebU z n ∈ ℂ⟮z⟯` and `K(z) ∈ ℂ⟮z⟯`. -/
private theorem twistParam_mem_adjoin_simple {Ω : Type*} [Field Ω] [Algebra ℂ Ω] (m : ℕ)
    (z : Ω) : z - ((chebU z (m - 1) - chebU z m) * chebU z (m - 1))⁻¹ ∈ ℂ⟮z⟯ := by
  have hU : ∀ n : ℕ, chebU z n ∈ ℂ⟮z⟯ := fun n ↦ by
    have h := chebU_map_ringHom_eq (algebraMap ℂ⟮z⟯ Ω) (AdjoinSimple.gen ℂ z) n
    rw [AdjoinSimple.algebraMap_gen] at h
    rw [← h]
    exact Subtype.mem _
  exact sub_mem (mem_adjoin_simple_self ℂ z)
    (inv_mem (mul_mem (sub_mem (hU _) (hU _)) (hU _)))

/-- `[ℂ(M) : ℂ(K)] ≤ 4` when `M⁴ - K M² + 1 = 0`. -/
private theorem relfinrank_adjoin_le_four {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {M K : Ω}
    (hM4 : M ^ 4 - K * M ^ 2 + 1 = 0) (hKM : ℂ⟮K⟯ ≤ ℂ⟮M⟯) : relfinrank ℂ⟮K⟯ ℂ⟮M⟯ ≤ 4 := by
  rw [← sup_eq_right.mpr hKM, relfinrank_sup_adjoin_simple]
  set b : ℂ⟮K⟯ := AdjoinSimple.gen ℂ K
  have hmon : (X ^ 4 - C b * X ^ 2 + 1 : ℂ⟮K⟯[X]).Monic := by monicity!
  have hev : aeval M (X ^ 4 - C b * X ^ 2 + 1 : ℂ⟮K⟯[X]) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one,
      AdjoinSimple.algebraMap_gen, b]
    exact hM4
  rw [adjoin.finrank ⟨_, hmon, hev⟩]
  calc (minpoly ℂ⟮K⟯ M).natDegree ≤ (X ^ 4 - C b * X ^ 2 + 1 : ℂ⟮K⟯[X]).natDegree :=
        natDegree_le_natDegree (minpoly.min _ _ hmon hev)
    _ = 4 := by compute_degree!

/-- `2m ≤ [ℂ(M, z) : ℂ(M)]`: from `[ℂ(z, M) : ℂ(K)] = 4 · 2m` and `[ℂ(M) : ℂ(K)] ≤ 4`. -/
private theorem two_mul_le_natDegree_minpoly_of_twistParam {Ω : Type*} [Field Ω]
    [Algebra ℂ Ω] {m : ℕ} (hm : 2 ≤ m) {M K z : Ω} (hz : Transcendental ℂ z)
    (hM4 : M ^ 4 - K * M ^ 2 + 1 = 0)
    (hK : K = z - ((chebU z (m - 1) - chebU z m) * chebU z (m - 1))⁻¹)
    (hint : IsIntegral ℂ⟮M⟯ z) :
    2 * m ≤ (minpoly ℂ⟮M⟯ z).natDegree := by
  have hM0 : M ≠ 0 := by
    rintro rfl
    norm_num at hM4
  have hKz : ℂ⟮K⟯ ≤ ℂ⟮z⟯ := by
    rw [adjoin_simple_le_iff, hK]
    exact twistParam_mem_adjoin_simple m z
  have hKM : ℂ⟮K⟯ ≤ ℂ⟮M⟯ := by
    have hK' : K = (M ^ 4 + 1) / M ^ 2 := by
      field_simp
      linear_combination -hM4
    rw [adjoin_simple_le_iff, hK']
    have hMm := mem_adjoin_simple_self ℂ M
    exact div_mem (add_mem (pow_mem hMm _) (one_mem _)) (pow_mem hMm _)
  have e1 := relfinrank_mul_relfinrank hKz (le_sup_left : ℂ⟮z⟯ ≤ ℂ⟮z⟯ ⊔ ℂ⟮M⟯)
  have e2 := relfinrank_mul_relfinrank hKM (le_sup_right : ℂ⟮M⟯ ≤ ℂ⟮z⟯ ⊔ ℂ⟮M⟯)
  rw [relfinrank_adjoin_twistParamK (by omega) hz hK,
    relfinrank_sup_adjoin_biquadratic hm hz hM4 hK] at e1
  have hr : relfinrank ℂ⟮M⟯ (ℂ⟮z⟯ ⊔ ℂ⟮M⟯) = (minpoly ℂ⟮M⟯ z).natDegree := by
    rw [sup_comm, relfinrank_sup_adjoin_simple, adjoin.finrank hint]
  rw [hr] at e2
  have h8 : 2 * m * 4 ≤ 4 * (minpoly ℂ⟮M⟯ z).natDegree := by
    rw [e1, ← e2]
    exact Nat.mul_le_mul_right _ (relfinrank_adjoin_le_four hM4 hKM)
  omega

/-- In a finite extension `Ω` of `ℂ(M)`, every `z` is integral over the image `ℂ⟮M⟯` of
`ℂ(M)`, of degree at most `[Ω : ℂ(M)]`. -/
private theorem natDegree_minpoly_adjoin_le_finrank {Ω : Type*} [Field Ω]
    [Algebra (RatFunc ℂ) Ω] [Algebra ℂ Ω] [IsScalarTower ℂ (RatFunc ℂ) Ω]
    [FiniteDimensional (RatFunc ℂ) Ω] (z : Ω) :
    IsIntegral ℂ⟮algebraMap (RatFunc ℂ) Ω RatFunc.X⟯ z ∧
      (minpoly ℂ⟮algebraMap (RatFunc ℂ) Ω RatFunc.X⟯ z).natDegree ≤
        Module.finrank (RatFunc ℂ) Ω := by
  set M := algebraMap (RatFunc ℂ) Ω RatFunc.X
  have hmem : ∀ a : RatFunc ℂ, algebraMap (RatFunc ℂ) Ω a ∈ ℂ⟮M⟯ := fun a ↦
    algHom_ratFunc_mem_adjoin (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) Ω) a
  set ι : RatFunc ℂ →+* ℂ⟮M⟯ := (algebraMap (RatFunc ℂ) Ω).codRestrict ℂ⟮M⟯ hmem
  have hcomp : (algebraMap ℂ⟮M⟯ Ω).comp ι = algebraMap (RatFunc ℂ) Ω :=
    RingHom.ext fun _ ↦ rfl
  set p := (minpoly (RatFunc ℂ) z).map ι
  have hmon : p.Monic := (minpoly.monic (Algebra.IsIntegral.isIntegral z)).map ι
  have hev : aeval z p = 0 := by
    rw [aeval_def, eval₂_map, hcomp, ← aeval_def, minpoly.aeval]
  refine ⟨⟨p, hmon, hev⟩, ?_⟩
  calc (minpoly ℂ⟮M⟯ z).natDegree ≤ p.natDegree :=
        natDegree_le_natDegree (minpoly.min _ _ hmon hev)
    _ = (minpoly (RatFunc ℂ) z).natDegree := natDegree_map ι
    _ ≤ _ := minpoly.natDegree_le z

/-- Every irreducible factor of `B_m` in `ℂ(M)[L]` has degree at least `2m`. -/
theorem two_mul_le_natDegree_of_dvd_twistPoly (m : ℕ) (hm : 2 ≤ m) {g : (RatFunc ℂ)[X]}
    (hg : Irreducible g)
    (hdvd : g ∣ (twistPoly m).map
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))) :
    2 * m ≤ g.natDegree := by
  have hg0 : g ≠ 0 := hg.ne_zero
  have : Fact (Irreducible g) := ⟨hg⟩
  have : FiniteDimensional (RatFunc ℂ) (AdjoinRoot g) := (AdjoinRoot.powerBasis hg0).finite
  have hfin : Module.finrank (RatFunc ℂ) (AdjoinRoot g) = g.natDegree := by
    rw [(AdjoinRoot.powerBasis hg0).finrank, AdjoinRoot.powerBasis_dim]
  set M : AdjoinRoot g := algebraMap (RatFunc ℂ) (AdjoinRoot g) RatFunc.X with hMdef
  have hL : aeval (AdjoinRoot.root g) ((twistPoly m).map
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))) = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  obtain ⟨-, -, hK⟩ := famParam_inverse (by omega) (famTK_eq_zero_of_twistPoly_root
    (by omega) hL)
  have hM0 : M ≠ 0 := by simp [M, RatFunc.X_ne_zero]
  have hM4 : M ^ 4 - famKQ (M ^ 2) * M ^ 2 + 1 = 0 := by
    simp only [famKQ]
    field_simp
    ring
  have hMtr : Transcendental ℂ M := by
    rw [hMdef, transcendental_algebraMap_iff (algebraMap (RatFunc ℂ) (AdjoinRoot g)).injective]
    exact RatFunc.transcendental_X
  have hz := transcendental_of_twistParam_eq hMtr hM4 hK
  obtain ⟨hint, hle⟩ := natDegree_minpoly_adjoin_le_finrank (Ω := AdjoinRoot g)
    (famZK (famKQ (M ^ 2)) ((M ^ 2 * AdjoinRoot.root g + 1) / (AdjoinRoot.root g + M ^ 2)))
  exact ((two_mul_le_natDegree_minpoly_of_twistParam hm hz hM4 hK hint).trans hle).trans_eq hfin

end AJConjecture
