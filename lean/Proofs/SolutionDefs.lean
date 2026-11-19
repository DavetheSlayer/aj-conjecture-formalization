import Mathlib
import AJHandoff.LocalTheory.LocSeqGerm
import AJHandoff.Geometry.GeoCurveFunctionField
import AJHandoff.Geometry.GeoK2Symbol
import AJHandoff.Geometry.GeoShapeRep
import AJHandoff.Geometry.GeoMarkPattern

/-!
# Replacement definitions for the solution `Solution.lean`

Some definitions of the library use `private` lemmas in their bodies (as proof arguments, or
through a public theorem whose proof uses one). A private name contains its module, so such a
definition cannot be copied identically into the challenge `Challenge`. This file has
public copies of those lemmas and theorems (same statements and proofs, names ending in `R`) and
replacement definitions (`…R`) whose statements and bodies are those of the library's definitions
except for the proof terms, which use the copies. Proofs are irrelevant to the kernel, so each
replacement is definitionally equal to the library's definition; the release theorems about the
replacements (`Solution.lean`) follow from the library's theorems.

* `ratRamifyR`, `ratPowerSubstR` (`LocRamification`, `LocPowerPullback`): for
  `hasSimpleResidue_ramify` and `hasNormalizedIndex_powerSubst`;
* `seqEvalR` (`LocSeqGerm`): for `seq_theoremS`;
* the instance `IsDomain GeoCoordE` and `geoRfunR` (`GeoCurveFunctionField`, `GeoCurveDegreeTwo`):
  for the function-field units of Theorem G;
* the instance `IsDomain GeoCoordEbar`, `geoMerBar_ne_zeroR`, `geoLongBar_ne_zeroR`
  (`GeoK2Symbol`): for G-K2;
* `geoPatternShapeRepR` (`GeoShapeMarking`, through `geoShapeRepR` and `geoPatToTilR`): for MARK.

The replacement instances have priority `high`, so that they are the instances found where the
release statements need `IsDomain GeoCoordE` or `IsDomain GeoCoordEbar` (the library's instances
are equal as proofs).
-/

noncomputable section

namespace AJConjecture

/-! ### From `AJHandoff/LocalTheory/LocRamification.lean` -/

section
open Polynomial

/-- Public copy of the private `nonZeroDivisors_le_comap_compRingHom_ramify`
(`LocRamification.lean`): same statement and proof. -/
theorem nonZeroDivisors_le_comap_compRingHom_ramifyR (z₀ : ℂ) {e : ℕ} (he : 0 < e) :
    nonZeroDivisors ℂ[X] ≤
      (nonZeroDivisors ℂ[X]).comap (Polynomial.compRingHom (C z₀ + X ^ e : ℂ[X])) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  intro h
  rcases comp_eq_zero_iff.1 h with h | ⟨-, h⟩
  · exact nonZeroDivisors.ne_zero hp h
  · have := congrArg natDegree h
    rw [natDegree_C, natDegree_C_add, natDegree_X_pow] at this
    omega

/-- Replacement for `ratRamify` (`LocRamification.lean`): statement and body identical except for
the proof terms, which use the public copies; definitionally equal to `ratRamify`. -/
def ratRamifyR (z₀ : ℂ) (e : ℕ) (he : 0 < e) : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.mapRingHom (Polynomial.compRingHom (C z₀ + X ^ e : ℂ[X]))
    (nonZeroDivisors_le_comap_compRingHom_ramifyR z₀ he)

end

/-! ### From `AJHandoff/LocalTheory/LocPowerPullback.lean` -/

section
open Polynomial

/-- Public copy of the private `nonZeroDivisors_le_comap_compRingHom_powerSubst`
(`LocPowerPullback.lean`): same statement and proof. -/
theorem nonZeroDivisors_le_comap_compRingHom_powerSubstR {a : ℂ} {k : ℕ} (ha : a ≠ 0)
    (hk : 0 < k) :
    nonZeroDivisors ℂ[X] ≤
      (nonZeroDivisors ℂ[X]).comap (Polynomial.compRingHom (C a * X ^ k : ℂ[X])) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  intro h
  rcases comp_eq_zero_iff.1 h with h | ⟨-, h⟩
  · exact nonZeroDivisors.ne_zero hp h
  · have := congrArg natDegree h
    rw [natDegree_C, natDegree_C_mul_X_pow k a ha] at this
    omega

/-- Replacement for `ratPowerSubst` (`LocPowerPullback.lean`): statement and body identical except
for the proof terms, which use the public copies; definitionally equal to `ratPowerSubst`. -/
def ratPowerSubstR (a : ℂ) (k : ℕ) (ha : a ≠ 0) (hk : 0 < k) : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.mapRingHom (Polynomial.compRingHom (C a * X ^ k : ℂ[X]))
    (nonZeroDivisors_le_comap_compRingHom_powerSubstR ha hk)

end

/-! ### From `AJConjecture/QAlgQParamBasic.lean` -/

section

/-- Public copy of the private `intDegree_ratFuncX_zpow_eq` (`QAlgQParamBasic.lean`): same statement
and proof. -/
theorem intDegree_ratFuncX_zpow_eqR (n : ℤ) :
    ((RatFunc.X : RatFunc ℚ) ^ n).intDegree = n := by
  have hnat : ∀ m : ℕ, ((RatFunc.X : RatFunc ℚ) ^ m).intDegree = m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero m RatFunc.X_ne_zero) RatFunc.X_ne_zero, ih,
        RatFunc.intDegree_X]
      push_cast
      rfl
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, hnat]
  · rw [zpow_neg, RatFunc.intDegree_inv, zpow_natCast, hnat]

/-- Copy of `ratFuncX_zpow_injective` (`QAlgQParamBasic.lean`): same statement and proof, with the
private lemmas it uses replaced by their public copies. -/
theorem ratFuncX_zpow_injectiveR :
    Function.Injective fun n : ℤ ↦ (RatFunc.X : RatFunc ℚ) ^ n := by
  intro m n h
  have h' := congrArg RatFunc.intDegree h
  simpa only [intDegree_ratFuncX_zpow_eqR] using h'

end

/-! ### From `AJConjecture/QAlgEvalAtFieldZeros.lean` -/

section
open Polynomial

/-- Public copy of the private `eval₂RingHom_intCast_ratFuncX_eq_comp`
(`QAlgEvalAtFieldZeros.lean`): same statement and proof. -/
theorem eval₂RingHom_intCast_ratFuncX_eq_compR :
    Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X =
      (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) := by
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · simp
  · simp [RatFunc.algebraMap_X]

/-- Public copy of the private `eval₂RingHom_intCast_ratFuncX_injective`
(`QAlgEvalAtFieldZeros.lean`): same statement and proof. -/
theorem eval₂RingHom_intCast_ratFuncX_injectiveR :
    Function.Injective (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X) := by
  rw [eval₂RingHom_intCast_ratFuncX_eq_compR, RingHom.coe_comp, coe_mapRingHom]
  exact (RatFunc.algebraMap_injective ℚ).comp (Polynomial.map_injective _ Int.cast_injective)

/-- Copy of `finite_setOf_evalAtField_eq_zero` (`QAlgEvalAtFieldZeros.lean`): same statement and
proof, with the private lemmas it uses replaced by their public copies. -/
theorem finite_setOf_evalAtField_eq_zeroR {c : Coeff} (hc : c ≠ 0) :
    {n : ℤ | evalAtField n c = 0}.Finite := by
  have hne : c.map (Polynomial.eval₂RingHom (Int.castRingHom (RatFunc ℚ)) RatFunc.X) ≠ 0 :=
    (Polynomial.map_ne_zero_iff eval₂RingHom_intCast_ratFuncX_injectiveR).mpr hc
  have hinj : Function.Injective fun n : ℤ ↦ (RatFunc.X : RatFunc ℚ) ^ (2 * n) := by
    intro m n h
    have h2 : 2 * m = 2 * n := ratFuncX_zpow_injectiveR h
    omega
  refine ((Polynomial.finite_setOfPred_isRoot hne).preimage hinj.injOn).subset fun n hn ↦ ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, IsRoot.def, eval_map]
  exact hn

/-- Copy of `exists_forall_ge_evalAtField_ne_zero` (`QAlgEvalAtFieldZeros.lean`): same statement and
proof, with the private lemmas it uses replaced by their public copies. -/
theorem exists_forall_ge_evalAtField_ne_zeroR {c : Coeff} (hc : c ≠ 0) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → evalAtField n c ≠ 0 := by
  obtain ⟨B, hB⟩ := (finite_setOf_evalAtField_eq_zeroR hc).bddAbove
  refine ⟨B + 1, fun n hn h ↦ ?_⟩
  have hle : n ≤ B := hB h
  omega

end

/-! ### From `AJHandoff/LocalTheory/LocSeqGerm.lean` -/

section
open Polynomial Filter

/-- Copy of `isUnit_seqGerm_evalAtField` (`LocSeqGerm.lean`): same statement and proof, with the
private lemmas it uses replaced by their public copies. -/
theorem isUnit_seqGerm_evalAtFieldR {c : Coeff} (hc : c ∈ nonZeroDivisors Coeff) :
    IsUnit (seqGerm fun n ↦ evalAtField n c) := by
  obtain ⟨n₀, hn₀⟩ := exists_forall_ge_evalAtField_ne_zeroR (nonZeroDivisors.ne_zero hc)
  refine IsUnit.of_mul_eq_one (seqGerm fun n ↦ (evalAtField n c)⁻¹) ?_
  rw [seqGerm, seqGerm, ← map_mul, ← map_one (Germ.coeRingHom atTop)]
  exact Germ.coe_eq.mpr <| Filter.eventually_atTop.mpr ⟨n₀, fun n hn ↦
    mul_inv_cancel₀ (hn₀ n hn)⟩

/-- Replacement for `seqEval` (`LocSeqGerm.lean`): statement and body identical except for the proof
terms, which use the public copies; definitionally equal to `seqEval`. -/
def seqEvalR : SeqField →+* SeqGerm :=
  IsLocalization.lift (M := nonZeroDivisors Coeff) (S := SeqField)
    (g := (Germ.coeRingHom atTop).comp (RingHom.pi fun n ↦ evalAtField n))
    (fun c ↦ isUnit_seqGerm_evalAtFieldR c.2)

end

/-! ### From `AJConjecture/ExtraFactorIrreducible.lean` -/

section
open Polynomial

/-- Public copy of the private `extraFactor_map_complex_eq` (`ExtraFactorIrreducible.lean`): same
statement and proof. -/
theorem extraFactor_map_complex_eqR :
    extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) =
      X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) := by
  simp [extraFactor]

/-- Public copy of the private `monomial_add_ne_extraFactor_trace` (`ExtraFactorIrreducible.lean`):
same statement and proof. -/
theorem monomial_add_ne_extraFactor_traceR (c : ℂ) (hc : c ≠ 0) (i : ℕ) (hi : i ≤ 4) :
    (C c * (C c * X ^ i) + X ^ (4 - i) : ℂ[X]) ≠ C c * (X ^ 4 - 4 * X ^ 2 + 1) := by
  intro h
  have h2 := congrArg (fun p : ℂ[X] ↦ p.coeff 2) h
  have h0 := congrArg (fun p : ℂ[X] ↦ p.coeff 0) h
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_one, coeff_ofNat_mul] at h0 h2
  clear h
  interval_cases i <;> simp_all

/-- Public copy of the private `extraFactor_quadratic_ne_zero` (`ExtraFactorIrreducible.lean`): same
statement and proof. -/
theorem extraFactor_quadratic_ne_zeroR (a : ℂ[X]) :
    a ^ 2 - (X ^ 4 - 4 * X ^ 2 + 1) * a + X ^ 4 ≠ 0 := by
  intro h
  have hab : a * ((X ^ 4 - 4 * X ^ 2 + 1) - a) = X ^ 4 := by linear_combination -h
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X _).mp (Dvd.intro _ hab)
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hc0 : c ≠ 0 := hc.ne_zero
  obtain rfl : a = C c * X ^ i := by rw [← hu, ← hcu, mul_comm]
  have hXi : (X ^ i : ℂ[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hsplit : (X ^ 4 : ℂ[X]) = X ^ i * X ^ (4 - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  have hb : C c * ((X ^ 4 - 4 * X ^ 2 + 1) - C c * X ^ i) = X ^ (4 - i) := by
    apply mul_left_cancel₀ hXi
    rw [← hsplit]
    linear_combination hab
  apply monomial_add_ne_extraFactor_traceR c hc0 i hi
  rw [← hb]
  ring

/-- Copy of `irreducible_extraFactor_map` (`ExtraFactorIrreducible.lean`): same statement and proof,
with the private lemmas it uses replaced by their public copies. -/
theorem irreducible_extraFactor_mapR :
    Irreducible (extraFactor.map (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
  rw [extraFactor_map_complex_eqR]
  have hdeg : (X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) : ℂ[X][X]).natDegree = 2 := by
    compute_degree!
  have hmonic : (X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) : ℂ[X][X]).Monic := by
    monicity!
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun a ha ↦ extraFactor_quadratic_ne_zeroR a ?_
  have hroot := (mem_roots hmonic.ne_zero).mp ha
  simpa [IsRoot.def] using hroot

end

/-! ### From `AJHandoff/Geometry/GeoCurveFunctionField.lean` -/

section
open Polynomial

/-- Public copy of the private `geo_extraFactorℚ_monic` (`GeoCurveFunctionField.lean`): same
statement and proof. -/
theorem geo_extraFactorℚ_monicR : geoExtraFactorℚ.Monic := by
  have hlin : (C (X ^ 4 - 4 * X ^ 2 + 1 : ℤ[X]) * X).degree < ((2 : ℕ) : WithBot ℕ) :=
    (degree_C_mul_X_le _).trans_lt (by norm_num)
  refine Monic.map _ ((monic_X_pow_sub hlin).add_of_left ?_)
  rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  exact degree_C_le.trans_lt (by norm_num)

/-- Public copy of the private `geo_irreducible_extraFactorℚ` (`GeoCurveFunctionField.lean`): same
statement and proof. -/
theorem geo_irreducible_extraFactorℚR : Irreducible geoExtraFactorℚ := by
  refine geo_extraFactorℚ_monicR.irreducible_of_irreducible_map
    (Polynomial.mapRingHom (algebraMap ℚ ℂ)) _ ?_
  rw [Polynomial.map_map]
  convert irreducible_extraFactor_mapR using 2
  ext <;> simp

/-- Copy of `geo_prime_extraFactorℚ` (`GeoCurveFunctionField.lean`): same statement and proof, with
the private lemmas it uses replaced by their public copies. -/
theorem geo_prime_extraFactorℚR : Prime geoExtraFactorℚ :=
  geo_irreducible_extraFactorℚR.prime

/-- Replacement for the library's instance `IsDomain GeoCoordE` (`GeoCurveFunctionField.lean`): same
statement, proof through the public copies; priority `high`. -/
instance (priority := high) instIsDomainGeoCoordER : IsDomain GeoCoordE :=
  AdjoinRoot.isDomain_of_prime geo_prime_extraFactorℚR

end

/-! ### From `AJHandoff/Geometry/GeoCurveDegreeTwo.lean` -/

section
open Polynomial

/-- Replacement for `geoRfun` (`GeoCurveDegreeTwo.lean`): statement and body identical except for
the proof terms, which use the public copies; definitionally equal to `geoRfun`. -/
def geoRfunR : GeoFunFieldE :=
  (algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 + algebraMap GeoCoordE GeoFunFieldE geoLong) /
    (algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 *
      (algebraMap GeoCoordE GeoFunFieldE geoMer ^ 2 - 1))

end

/-! ### From `AJHandoff/Geometry/GeoK2Symbol.lean` -/

section
open Polynomial TensorProduct

/-- Public copy of the private `geoExtraFactorQbar_eq` (`GeoK2Symbol.lean`): same statement and
proof. -/
theorem geoExtraFactorQbar_eqR :
    geoExtraFactorQbar = X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) := by
  simp [geoExtraFactorQbar, extraFactor]

/-- Public copy of the private `geoExtraFactorQbar_natDegree` (`GeoK2Symbol.lean`): same statement
and proof. -/
theorem geoExtraFactorQbar_natDegreeR : geoExtraFactorQbar.natDegree = 2 := by
  rw [geoExtraFactorQbar_eqR]
  compute_degree!

/-- Public copy of the private `geo_monomial_add_ne_trace_Qbar` (`GeoK2Symbol.lean`): same statement
and proof. -/
theorem geo_monomial_add_ne_trace_QbarR (c : AlgebraicClosure ℚ) (hc : c ≠ 0) (i : ℕ)
    (hi : i ≤ 4) :
    (C c * (C c * X ^ i) + X ^ (4 - i) : (AlgebraicClosure ℚ)[X]) ≠
      C c * (X ^ 4 - 4 * X ^ 2 + 1) := by
  intro h
  have h2 := congrArg (fun p : (AlgebraicClosure ℚ)[X] ↦ p.coeff 2) h
  have h0 := congrArg (fun p : (AlgebraicClosure ℚ)[X] ↦ p.coeff 0) h
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_one, coeff_ofNat_mul] at h0 h2
  clear h
  interval_cases i <;> simp_all

/-- Public copy of the private `geo_extraFactorQbar_no_root` (`GeoK2Symbol.lean`): same statement
and proof. -/
theorem geo_extraFactorQbar_no_rootR (a : (AlgebraicClosure ℚ)[X]) :
    a ^ 2 - (X ^ 4 - 4 * X ^ 2 + 1) * a + X ^ 4 ≠ 0 := by
  intro h
  have hab : a * ((X ^ 4 - 4 * X ^ 2 + 1) - a) = X ^ 4 := by linear_combination -h
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X _).mp (Dvd.intro _ hab)
  obtain ⟨u, hu⟩ := hassoc.symm
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hc0 : c ≠ 0 := hc.ne_zero
  obtain rfl : a = C c * X ^ i := by rw [← hu, ← hcu, mul_comm]
  have hXi : (X ^ i : (AlgebraicClosure ℚ)[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hsplit : (X ^ 4 : (AlgebraicClosure ℚ)[X]) = X ^ i * X ^ (4 - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  have hb : C c * ((X ^ 4 - 4 * X ^ 2 + 1) - C c * X ^ i) = X ^ (4 - i) := by
    apply mul_left_cancel₀ hXi
    rw [← hsplit]
    linear_combination hab
  apply geo_monomial_add_ne_trace_QbarR c hc0 i hi
  rw [← hb]
  ring

/-- Copy of `geo_prime_extraFactorQbar` (`GeoK2Symbol.lean`): same statement and proof, with the
private lemmas it uses replaced by their public copies. -/
theorem geo_prime_extraFactorQbarR : Prime geoExtraFactorQbar := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime, geoExtraFactorQbar_eqR]
  have hmonic : (X ^ 2 - C (X ^ 4 - 4 * X ^ 2 + 1) * X + C (X ^ 4) :
      (AlgebraicClosure ℚ)[X][X]).Monic := by
    monicity!
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by
    rw [← geoExtraFactorQbar_eqR, geoExtraFactorQbar_natDegreeR]) (by
    rw [← geoExtraFactorQbar_eqR, geoExtraFactorQbar_natDegreeR]; omega)]
  refine Multiset.eq_zero_of_forall_notMem fun a ha ↦ geo_extraFactorQbar_no_rootR a ?_
  have hroot := (mem_roots hmonic.ne_zero).mp ha
  simpa [IsRoot.def] using hroot

/-- Replacement for the library's instance `IsDomain GeoCoordEbar` (`GeoK2Symbol.lean`): same
statement, proof through the public copies; priority `high`. -/
instance (priority := high) instIsDomainGeoCoordEbarR : IsDomain GeoCoordEbar :=
  AdjoinRoot.isDomain_of_prime geo_prime_extraFactorQbarR

/-- Public copy of the private `geo_algebraMap_of_ne_zero_Qbar` (`GeoK2Symbol.lean`): same statement
and proof. -/
theorem geo_algebraMap_of_ne_zero_QbarR (p : (AlgebraicClosure ℚ)[X]) (hp : p ≠ 0) :
    algebraMap GeoCoordEbar GeoFunFieldEbar (AdjoinRoot.of _ p) ≠ 0 := by
  rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _), AdjoinRoot.of,
    RingHom.comp_apply, AdjoinRoot.mk_eq_zero]
  intro h
  have h' := Polynomial.natDegree_le_of_dvd h (C_ne_zero.mpr hp)
  rw [geoExtraFactorQbar_natDegreeR, natDegree_C] at h'
  omega

/-- Copy of `geoMerBar_ne_zero` (`GeoK2Symbol.lean`): same statement and proof, with the private
lemmas it uses replaced by their public copies. -/
theorem geoMerBar_ne_zeroR : geoMerBar ≠ 0 :=
  geo_algebraMap_of_ne_zero_QbarR X X_ne_zero

/-- Copy of `geoLongBar_ne_zero` (`GeoK2Symbol.lean`): same statement; the proof is the library's
with the private lemmas replaced by their public copies and the definition unfolded by
`show`/`delta` instead of its equation lemma. -/
theorem geoLongBar_ne_zeroR : geoLongBar ≠ 0 := by
  show algebraMap GeoCoordEbar GeoFunFieldEbar (AdjoinRoot.root geoExtraFactorQbar) ≠ 0
  rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _), AdjoinRoot.root,
    AdjoinRoot.mk_eq_zero]
  intro h
  have h' := Polynomial.natDegree_le_of_dvd h X_ne_zero
  rw [geoExtraFactorQbar_natDegreeR, natDegree_X] at h'
  omega

end

/-! ### From `AJHandoff/Geometry/GeoMarkGroups.lean` -/

section

/-- Public copy of the private `geo_tillmann_rel` (`GeoMarkGroups.lean`): same statement and proof.
-/
theorem geo_tillmann_relR :
    geoTilB * geoTilA * geoTilB * geoTilA⁻¹ * geoTilB⁻¹ * geoTilA⁻¹ * geoTilB * geoTilA *
        (geoTilA * geoTilB * geoTilA⁻¹ * geoTilB⁻¹ * geoTilA⁻¹ * geoTilB * geoTilA * geoTilB)⁻¹ =
      1 := by
  have h := PresentedGroup.one_of_mem (rels := ({geoTilRel} : Set (FreeGroup (Fin 2))))
    (Set.mem_singleton geoTilRel)
  exact h

/-- Copy of `geo_tillmann_relation` (`GeoMarkGroups.lean`): same statement and proof, with the
private lemmas it uses replaced by their public copies. -/
theorem geo_tillmann_relationR :
    geoTilB * geoTilA * geoTilB * geoTilA⁻¹ * geoTilB⁻¹ * geoTilA⁻¹ * geoTilB * geoTilA *
        (geoTilA * geoTilB * geoTilA⁻¹ * geoTilB⁻¹ * geoTilA⁻¹ * geoTilB * geoTilA * geoTilB)⁻¹ =
      1 :=
  geo_tillmann_relR

end

/-! ### From `AJHandoff/Geometry/GeoMarkPattern.lean` -/

section

/-- Public copy of the private `geo_pat_conj_zpow_eq_one` (`GeoMarkPattern.lean`): same statement
and proof. -/
theorem geo_pat_conj_zpow_eq_oneR {G : Type*} [Group G] {r : G} (g : G) (h : r = 1)
    (n : ℤ) : g * r ^ n * g⁻¹ = 1 := by
  rw [h, one_zpow, mul_one, mul_inv_cancel]

/-- Copy of `geo_patToTil_rel` (`GeoMarkPattern.lean`): same statement; the proof is the library's
with the private lemmas replaced by their public copies and the definition unfolded by
`show`/`delta` instead of its equation lemma. -/
theorem geo_patToTil_relR :
    FreeGroup.lift (![geoTilB, geoTilA⁻¹] : Fin 2 → GeoTillmannGroup) geoPatRel = 1 := by
  delta geoPatRel
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hR := geo_tillmann_relationR
  set a := geoTilA
  set b := geoTilB
  calc _ = (b * a * b⁻¹ * a⁻¹ * b⁻¹) * (b * a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a *
        (a * b * a⁻¹ * b⁻¹ * a⁻¹ * b * a * b)⁻¹) ^ (-1 : ℤ) *
        (b * a * b⁻¹ * a⁻¹ * b⁻¹)⁻¹ := by group
    _ = 1 := geo_pat_conj_zpow_eq_oneR _ hR _

/-- Replacement for `geoPatToTil` (`GeoMarkPattern.lean`): statement and body identical except for
the proof terms, which use the public copies; definitionally equal to `geoPatToTil`. -/
def geoPatToTilR : GeoPatternGroup →* GeoTillmannGroup :=
  PresentedGroup.toGroup (by rintro r rfl; exact geo_patToTil_relR)

end

/-! ### From `AJHandoff/Geometry/GeoShapeRep.lean` -/

section
open Matrix

/-- Public copy of the private `geo_shapeA_coe` (`GeoShapeRep.lean`): same statement and proof. -/
theorem geo_shapeA_coeR (w : ℂ) :
    ((geoShapeA w : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1, -(1 + w) / w; 0, 1] := rfl

/-- Public copy of the private `geo_shapeA_inv_coe` (`GeoShapeRep.lean`): same statement and proof.
-/
theorem geo_shapeA_inv_coeR (w : ℂ) :
    (((geoShapeA w)⁻¹ : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1, (1 + w) / w; 0, 1] := by
  change Matrix.adjugate !![1, -(1 + w) / w; 0, 1] = _
  rw [Matrix.adjugate_fin_two_of]
  simp only [neg_div, neg_neg, neg_zero]

/-- Public copy of the private `geo_shapeB_coe` (`GeoShapeRep.lean`): same statement and proof. -/
theorem geo_shapeB_coeR (u : ℂ) (hu : u ≠ 0) :
    ((geoShapeB u hu : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![u, 0; u⁻¹, u⁻¹] := rfl

/-- Public copy of the private `geo_shapeB_inv_coe` (`GeoShapeRep.lean`): same statement and proof.
-/
theorem geo_shapeB_inv_coeR (u : ℂ) (hu : u ≠ 0) :
    (((geoShapeB u hu)⁻¹ : SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![u⁻¹, 0; -u⁻¹, u] := by
  change Matrix.adjugate !![u, 0; u⁻¹, u⁻¹] = _
  rw [Matrix.adjugate_fin_two_of]
  simp only [neg_zero]

/-- Copy of `geo_shapeRep_rel` (`GeoShapeRep.lean`): same statement and proof, with the private
lemmas it uses replaced by their public copies. -/
theorem geo_shapeRep_relR {w u : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
    (hu : u ^ 2 = (1 + w) / (w * (1 - w))) :
    FreeGroup.lift (![geoShapeA w, geoShapeB u (geo_shape_u_ne_zero hw0 hw1 hwm1 hu)] :
      Fin 2 → SpecialLinearGroup (Fin 2) ℂ) geoTilRel = 1 := by
  have hu0 := geo_shape_u_ne_zero hw0 hw1 hwm1 hu
  simp only [geoTilRel, map_mul, map_inv, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [mul_inv_eq_one]
  have w1' : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hu' : u ^ 2 * (w * (1 - w)) = 1 + w := by rw [hu]; field_simp
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, geo_shapeA_coeR, geo_shapeA_inv_coeR,
    geo_shapeB_coeR, geo_shapeB_inv_coeR, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
    field_simp
    linear_combination (-w^2 - 2*w - 1) * hu'
  · simp
    field_simp
    linear_combination (u^2*w^2 + 2*u^2*w + u^2 - w^2 - 2*w - 1) * hu'
  · simp
    field_simp
    ring
  · simp
    field_simp
    linear_combination (w^2 + 2*w + 1) * hu'

/-- Replacement for `geoShapeRep` (`GeoShapeRep.lean`): statement and body identical except for the
proof terms, which use the public copies; definitionally equal to `geoShapeRep`. -/
def geoShapeRepR (w u : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
    (hu : u ^ 2 = (1 + w) / (w * (1 - w))) :
    GeoTillmannGroup →* SpecialLinearGroup (Fin 2) ℂ :=
  PresentedGroup.toGroup (by rintro r rfl; exact geo_shapeRep_relR hw0 hw1 hwm1 hu)

end

/-! ### From `AJHandoff/Geometry/GeoShapeMarking.lean` -/

section
open Matrix

/-- Replacement for `geoPatternShapeRep` (`GeoShapeMarking.lean`): statement and body identical
except for the proof terms, which use the public copies; definitionally equal to
`geoPatternShapeRep`. -/
def geoPatternShapeRepR (w u : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (hwm1 : w ≠ -1)
    (hu : u ^ 2 = (1 + w) / (w * (1 - w))) :
    GeoPatternGroup →* SpecialLinearGroup (Fin 2) ℂ :=
  (geoShapeRepR w u hw0 hw1 hwm1 hu).comp geoPatToTilR

end

end AJConjecture
