import Mathlib
import AJTwist.Quantum.TwQTwistPolyNegFacts
import AJTwist.Factor.TwFNegParam

/-!
# A root of `C_b` over `ℂ(M)` and its trace parameter (TwF, unit F2)

Source: revision 5, Section 5.1 (`operators.tex`): "Hence `z`, and also `J` which recovers `z`
together with `K`, has degree `2b - 1` over `ℂ(K)`. … the longitude change is invertible at
generic `M` and the value `C_b(x, -x)` excludes any extra clearing factor."

For a root `L` of `C_b` in an extension `Ω` of `ℂ(M)`, with `M` the image of the variable:

* `famTKNeg_eq_zero_of_twistPolyNeg_root`: `L + M² ≠ 0` and `T_(-b)(K, J) = 0` for
  `K = M² + M⁻²`, `J = (M² L + 1)/(L + M²)`.
* `transcendental_of_twistParamNeg_eq`: if `M` is transcendental over `ℂ`, `M⁴ - K M² + 1 = 0`
  and `K = z - 1/(A(z) B(z))`, then `z` is transcendental.
* `relfinrank_adjoin_twistParamNegK`: for transcendental `z` and `K = z - 1/(A(z) B(z))`:
  `[ℂ(z) : ℂ(K)] = 2b - 1`.

Route: the private lemmas `aeval_map_twistPoly_eq_evalEval`, `root_add_sq_ne_zero_of_twistPoly`,
`famTK_eq_zero_of_twistPoly_root`, `transcendental_of_twistParam_eq`,
`algHom_ratFunc_twistParamK`, `relfinrank_adjoin_twistParamK` of
`AJFamily/Quantum/TwistPolyFactorDegree.lean`, with `twistPoly → twistPolyNeg`
(`eval_neg_twistPolyNeg` for `L ≠ -M²`, `evalEval_twistPolyNeg`), `chebU z (m - 1) - chebU z m`,
`chebU z (m - 1)` replaced by `twfChebV z b - twfChebV z (b - 1)`, `twfChebV z b`, and
`finrank_twistParamK → finrank_twistParamNegK`.
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Ring homomorphisms commute with `twfChebV`. -/
private theorem twfChebV_map_ringHom_twfNegFactorRoot {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : R) : ∀ n : ℕ, f (twfChebV z n) = twfChebV (f z) n
  | 0 => by simp [twfChebV]
  | 1 => by simp [twfChebV]
  | n + 2 => by
    rw [twfChebV, twfChebV, map_sub, map_mul, twfChebV_map_ringHom_twfNegFactorRoot f z (n + 1),
      twfChebV_map_ringHom_twfNegFactorRoot f z n]

/-- A `ℂ`-algebra map out of `RatFunc ℂ` sends a polynomial to its evaluation at the image
of `X`. -/
private theorem algHom_ratFunc_algebraMap_twfNegFactorRoot {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (φ : RatFunc ℂ →ₐ[ℂ] Ω) (p : ℂ[X]) :
    φ (algebraMap ℂ[X] (RatFunc ℂ) p) = aeval (φ RatFunc.X) p := by
  have h : φ.comp (IsScalarTower.toAlgHom ℂ ℂ[X] (RatFunc ℂ)) = aeval (φ RatFunc.X) := by
    refine Polynomial.algHom_ext ?_
    simp [RatFunc.algebraMap_X]
  exact congrArg (fun ψ : ℂ[X] →ₐ[ℂ] Ω ↦ ψ p) h

/-- Evaluating the image of `twistPolyNeg k` in `ℂ(M)[L]` at a point `L` of a `ℂ(M)`-algebra `Ω`
is the bivariate evaluation at `(M, L)`. -/
private theorem aeval_map_twistPolyNeg_eq_evalEval_twfNegFactorRoot {Ω : Type*} [Field Ω]
    [Algebra (RatFunc ℂ) Ω] (k : ℕ) (L : Ω) :
    aeval L ((twistPolyNeg k).map
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))) =
    ((twistPolyNeg k).map (Polynomial.mapRingHom (Int.castRingHom Ω))).evalEval
      (algebraMap (RatFunc ℂ) Ω RatFunc.X) L := by
  set M := algebraMap (RatFunc ℂ) Ω RatFunc.X
  have hhom : (algebraMap (RatFunc ℂ) Ω).comp
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ))) =
      (evalRingHom M).comp (Polynomial.mapRingHom (Int.castRingHom Ω)) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp
    · simp [M, RatFunc.algebraMap_X]
  have hrhs : ((twistPolyNeg k).map (Polynomial.mapRingHom (Int.castRingHom Ω))).evalEval M L =
      (twistPolyNeg k).eval₂
        ((evalRingHom M).comp (Polynomial.mapRingHom (Int.castRingHom Ω))) L := by
    rw [evalEval, ← coe_evalRingHom, eval, hom_eval₂, eval₂_map]
    simp
  rw [hrhs, aeval_def, eval₂_map, hhom]

/-- At a root `L` of `C_b` in a field `Ω` over `ℂ(M)`, `L + M² ≠ 0`, because
`C_b(M, -M²) = M^(2b) (M⁴ - 1)^(2b-1) ≠ 0`. -/
private theorem root_add_sq_ne_zero_of_twistPolyNeg_twfNegFactorRoot {Ω : Type*} [Field Ω]
    [Algebra (RatFunc ℂ) Ω] {b : ℕ} (hb : 1 ≤ b) {L : Ω} (hL : aeval L ((twistPolyNeg b).map
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
  rw [aeval_def, eval₂_map, ← hψ, hLx, eval₂_at_apply, eval_neg_twistPolyNeg b hb] at hL
  have h0 := hinj (hL.trans (map_zero ψ).symm)
  have h1 : (X ^ 4 - 1 : ℤ[X]) ≠ 0 := fun h ↦ by simpa using congrArg (eval 0) h
  exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ h1) h0

/-- At a root `L` of `C_b` over `ℂ(M)`: `L + M² ≠ 0` and `T_(-b)(K, J) = 0`. -/
theorem famTKNeg_eq_zero_of_twistPolyNeg_root {Ω : Type*} [Field Ω] [Algebra (RatFunc ℂ) Ω]
    {b : ℕ} (hb : 1 ≤ b) {L : Ω}
    (hL : aeval L ((twistPolyNeg b).map
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))) = 0) :
    L + (algebraMap (RatFunc ℂ) Ω RatFunc.X) ^ 2 ≠ 0 ∧
      famTKNeg b (famKQ ((algebraMap (RatFunc ℂ) Ω RatFunc.X) ^ 2))
        (((algebraMap (RatFunc ℂ) Ω RatFunc.X) ^ 2 * L + 1) /
          (L + (algebraMap (RatFunc ℂ) Ω RatFunc.X) ^ 2)) = 0 := by
  have hM : algebraMap (RatFunc ℂ) Ω RatFunc.X ≠ 0 := by
    simp [RatFunc.X_ne_zero]
  have hL' := root_add_sq_ne_zero_of_twistPolyNeg_twfNegFactorRoot hb hL
  rw [aeval_map_twistPolyNeg_eq_evalEval_twfNegFactorRoot, evalEval_twistPolyNeg hM hL' hb] at hL
  exact ⟨hL', (mul_eq_zero.mp hL).resolve_left
    (mul_ne_zero (pow_ne_zero _ hL') (pow_ne_zero _ (pow_ne_zero _ hM)))⟩

/-- The trace parameter `z` of a transcendental meridian is transcendental. -/
theorem transcendental_of_twistParamNeg_eq {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {b : ℕ}
    {M K z : Ω} (hM : Transcendental ℂ M) (hM4 : M ^ 4 - K * M ^ 2 + 1 = 0)
    (hK : K = z - ((twfChebV z b - twfChebV z (b - 1)) * twfChebV z b)⁻¹) :
    Transcendental ℂ z := by
  intro hz
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one ℂ z
    (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hz.isIntegral))
  set k : ℂ := c - ((twfChebV c b - twfChebV c (b - 1)) * twfChebV c b)⁻¹
  have hk : K = algebraMap ℂ Ω k := by
    rw [hK, ← hc]
    simp only [k, map_sub, map_mul, map_inv₀, twfChebV_map_ringHom_twfNegFactorRoot]
  refine hM ⟨X ^ 4 - C k * X ^ 2 + 1, ?_, ?_⟩
  · have : (X ^ 4 - C k * X ^ 2 + 1 : ℂ[X]).natDegree = 4 := by compute_degree!
    intro h
    rw [h, natDegree_zero] at this
    exact absurd this (by norm_num)
  · simp [← hk, hM4]

/-- The `ℂ`-algebra map `RatFunc ℂ → Ω`, `X ↦ z`, sends `twistParamNegK b` to
`z - ((V_b(z) - V_(b-1)(z)) V_b(z))⁻¹`. -/
private theorem algHom_ratFunc_twistParamNegK_twfNegFactorRoot {Ω : Type*} [Field Ω]
    [Algebra ℂ Ω] (φ : RatFunc ℂ →ₐ[ℂ] Ω) (b : ℕ) :
    φ (twistParamNegK b) = φ RatFunc.X -
      ((twfChebV (φ RatFunc.X) b - twfChebV (φ RatFunc.X) (b - 1)) *
        twfChebV (φ RatFunc.X) b)⁻¹ := by
  have hU : ∀ n : ℕ, aeval (φ RatFunc.X) (twfChebV (X : ℂ[X]) n) = twfChebV (φ RatFunc.X) n := by
    intro n
    have h := twfChebV_map_ringHom_twfNegFactorRoot (aeval (φ RatFunc.X)).toRingHom (X : ℂ[X]) n
    simpa using h
  rw [twistParamNegK, map_sub, map_inv₀, algHom_ratFunc_algebraMap_twfNegFactorRoot, map_mul,
    map_sub, hU, hU]

/-- `[ℂ(z) : ℂ(K)] = 2b - 1` for transcendental `z` and `K = z - 1/(A(z) B(z))`. -/
theorem relfinrank_adjoin_twistParamNegK {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {b : ℕ}
    (hb : 1 ≤ b) {K z : Ω} (hz : Transcendental ℂ z)
    (hK : K = z - ((twfChebV z b - twfChebV z (b - 1)) * twfChebV z b)⁻¹) :
    relfinrank ℂ⟮K⟯ ℂ⟮z⟯ = 2 * b - 1 := by
  set f : RatFunc ℂ →ₐ[ℂ] Ω := ℂ⟮z⟯.val.comp (RatFunc.algEquivOfTranscendental z hz).toAlgHom
  have hfX : f RatFunc.X = z := by simp [f]
  have hfK : f (twistParamNegK b) = K := by
    rw [algHom_ratFunc_twistParamNegK_twfNegFactorRoot, hfX, hK]
  have h1 : ℂ⟮K⟯ = (ℂ⟮twistParamNegK b⟯).map f := by
    rw [adjoin_map, Set.image_singleton, hfK]
  have h2 : ℂ⟮z⟯ = (⊤ : IntermediateField ℂ (RatFunc ℂ)).map f := by
    rw [← AlgHom.fieldRange_eq_map]
    refine le_antisymm (adjoin_simple_le_iff.mpr ⟨RatFunc.X, hfX⟩) ?_
    rintro _ ⟨r, rfl⟩
    exact ((RatFunc.algEquivOfTranscendental z hz) r).2
  rw [h1, h2, relfinrank_map_map, relfinrank_top_right, finrank_twistParamNegK b hb]

end AJConjecture
