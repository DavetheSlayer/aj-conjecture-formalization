import Mathlib
import AJTwist.Factor.TwFNegFactorRoot

/-!
# Every factor of `C_b` over `ℂ(M)` has full degree (TwF, unit F2, crux)

Source: revision 5, Section 5.1: "Hence `z`, and also `J` which recovers `z` together with `K`,
has degree `2b - 1` over `ℂ(K)`. The extension `ℂ(M)/ℂ(K)` has degree four. The compositum degree
is a multiple of both degrees and is at most their product, so the odd degree `2b - 1` is
retained over `ℂ(M)`. The equation `T_(-b)` has that degree in `J`; the longitude change is
invertible at generic `M` and the value `C_b(x, -x)` excludes any extra clearing factor."

* `natDegree_minpoly_of_twistParamNeg`: if `z` is transcendental, `M⁴ - K M² + 1 = 0`,
  `K = z - 1/(A(z) B(z))` and `z` is integral over `ℂ(M)`, then the minimal polynomial of `z` over
  `ℂ(M)` has degree at least `2b - 1`.
* `natDegree_le_of_dvd_twistPolyNeg`: an irreducible factor `g` of `C_b` in `ℂ(M)[L]` has degree
  at least `2b - 1`.

Route: `two_mul_le_natDegree_minpoly_of_twistParam` and `two_mul_le_natDegree_of_dvd_twistPoly`
(`AJFamily/Quantum/TwistPolyFactorDegree.lean`), whose private lemmas
(`relfinrank_sup_adjoin_simple`, `twistParam_mem_adjoin_simple`, `relfinrank_adjoin_le_four`,
`natDegree_minpoly_adjoin_le_finrank`, `algHom_ratFunc_mem_adjoin`) are restated with the suffix
`_twfNeg`. Let `l` be a root of `g` in `Ω = AdjoinRoot g`; with `J = (M² l + 1)/(l + M²)`,
`K = M² + M⁻²`, `z = Z(K, J)`: `T_(-b)(K, J) = 0` (`famTKNeg_eq_zero_of_twistPolyNeg_root`), so
`K = z - 1/(A(z) B(z))` (`famParamNeg_inverse`), `z` is transcendental
(`transcendental_of_twistParamNeg_eq`) and `[ℂ(z) : ℂ(K)] = 2b - 1`
(`relfinrank_adjoin_twistParamNegK`). The degree `[ℂ(M) : ℂ(K)]` is `1`, `2` or `4` (`M²` is a
root of `X² - K X + 1` over `ℂ(K)` and `M` a root of `X² - M²` over `ℂ(M²)`: two steps of degree
at most `2`), hence coprime to the odd number `2b - 1`. Since `2b - 1` divides
`[ℂ(M, z) : ℂ(K)] = [ℂ(M, z) : ℂ(M)] · [ℂ(M) : ℂ(K)]`, it divides `[ℂ(M, z) : ℂ(M)]`, the degree
of the minimal polynomial of `z` over `ℂ(M)`, which is at most `[ℂ(M, l) : ℂ(M)] = deg g`
because `z ∈ ℂ(M, l)`.
This replaces the "not a square" step of the positive case (`TwistParamNotSquare.lean`,
`BiquadraticIrreducible.lean`), which is not needed here because the degree is odd.
Checked: `C_b` is irreducible over `ℚ(M)` for `b ≤ 5` (scratch `check_blocks.py`).
-/

open Polynomial IntermediateField

noncomputable section

namespace AJConjecture

/-- Ring homomorphisms commute with `twfChebV`. -/
private theorem twfChebV_map_ringHom_twfNeg {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : R) : ∀ n : ℕ, f (twfChebV z n) = twfChebV (f z) n
  | 0 => by simp [twfChebV]
  | 1 => by simp [twfChebV]
  | n + 2 => by
    rw [twfChebV, twfChebV, map_sub, map_mul, twfChebV_map_ringHom_twfNeg f z (n + 1),
      twfChebV_map_ringHom_twfNeg f z n]

/-- A `ℂ`-algebra map out of `RatFunc ℂ` sends a polynomial to its evaluation at the image
of `X`. -/
private theorem algHom_ratFunc_algebraMap_twfNeg {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (φ : RatFunc ℂ →ₐ[ℂ] Ω) (p : ℂ[X]) :
    φ (algebraMap ℂ[X] (RatFunc ℂ) p) = aeval (φ RatFunc.X) p := by
  have h : φ.comp (IsScalarTower.toAlgHom ℂ ℂ[X] (RatFunc ℂ)) = aeval (φ RatFunc.X) := by
    refine Polynomial.algHom_ext ?_
    simp [RatFunc.algebraMap_X]
  exact congrArg (fun ψ : ℂ[X] →ₐ[ℂ] Ω ↦ ψ p) h

/-- A polynomial evaluated at `y` lies in `ℂ⟮y⟯`. -/
private theorem aeval_mem_adjoin_simple_complex_twfNeg {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (y : Ω) (p : ℂ[X]) : aeval y p ∈ ℂ⟮y⟯ := by
  have h := aeval_algebraMap_apply Ω (AdjoinSimple.gen ℂ y) p
  rw [AdjoinSimple.algebraMap_gen] at h
  rw [h]
  exact Subtype.mem _

/-- The image of a `ℂ`-algebra map out of `RatFunc ℂ` lies in `ℂ⟮φ X⟯`. -/
private theorem algHom_ratFunc_mem_adjoin_twfNeg {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (φ : RatFunc ℂ →ₐ[ℂ] Ω) (r : RatFunc ℂ) : φ r ∈ ℂ⟮φ RatFunc.X⟯ := by
  rw [← RatFunc.num_div_denom r, map_div₀, algHom_ratFunc_algebraMap_twfNeg,
    algHom_ratFunc_algebraMap_twfNeg]
  exact div_mem (aeval_mem_adjoin_simple_complex_twfNeg _ _)
    (aeval_mem_adjoin_simple_complex_twfNeg _ _)

/-- The relative degree of `A ⊔ ℂ⟮y⟯` over `A` is the degree of `A⟮y⟯` over `A`. -/
private theorem relfinrank_sup_adjoin_simple_twfNeg {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (A : IntermediateField ℂ Ω) (y : Ω) :
    relfinrank A (A ⊔ ℂ⟮y⟯) = Module.finrank A A⟮y⟯ := by
  rw [relfinrank_eq_finrank_of_le le_sup_left]
  have h : extendScalars (le_sup_left : A ≤ A ⊔ ℂ⟮y⟯) = A⟮y⟯ := restrictScalars_injective ℂ <| by
    rw [extendScalars_restrictScalars, restrictScalars_adjoin_eq_sup]
  rw [h]

/-- `K(z) = z - 1/(A(z) B(z))` lies in `ℂ⟮z⟯`. -/
private theorem twistParamNeg_mem_adjoin_simple_twfNeg {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (b : ℕ) (z : Ω) :
    z - ((twfChebV z b - twfChebV z (b - 1)) * twfChebV z b)⁻¹ ∈ ℂ⟮z⟯ := by
  have hU : ∀ n : ℕ, twfChebV z n ∈ ℂ⟮z⟯ := fun n ↦ by
    have h := twfChebV_map_ringHom_twfNeg (algebraMap ℂ⟮z⟯ Ω) (AdjoinSimple.gen ℂ z) n
    rw [AdjoinSimple.algebraMap_gen] at h
    rw [← h]
    exact Subtype.mem _
  exact sub_mem (mem_adjoin_simple_self ℂ z)
    (inv_mem (mul_mem (sub_mem (hU _) (hU _)) (hU _)))

/-- Adjoining a root of a monic quadratic polynomial is a step of degree `1` or `2`. -/
private theorem relfinrank_sup_adjoin_quadratic_twfNeg {Ω : Type*} [Field Ω] [Algebra ℂ Ω]
    (A : IntermediateField ℂ Ω) (y : Ω) {p : A[X]} (hmon : p.Monic) (hdeg : p.natDegree = 2)
    (hev : aeval y p = 0) :
    relfinrank A (A ⊔ ℂ⟮y⟯) = 1 ∨ relfinrank A (A ⊔ ℂ⟮y⟯) = 2 := by
  have hint : IsIntegral A y := ⟨p, hmon, hev⟩
  rw [relfinrank_sup_adjoin_simple_twfNeg, adjoin.finrank hint]
  have hpos := minpoly.natDegree_pos hint
  have hle : (minpoly A y).natDegree ≤ 2 :=
    hdeg ▸ natDegree_le_natDegree (minpoly.min _ _ hmon hev)
  omega

/-- `[ℂ(M) : ℂ(K)]` is `1`, `2` or `4` when `M⁴ - K M² + 1 = 0`: two quadratic steps through
`ℂ(M²)`. -/
private theorem relfinrank_adjoin_pow_two_twfNeg {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {M K : Ω}
    (hM4 : M ^ 4 - K * M ^ 2 + 1 = 0) :
    ℂ⟮K⟯ ≤ ℂ⟮M⟯ ∧ ∃ j : ℕ, relfinrank ℂ⟮K⟯ ℂ⟮M⟯ = 2 ^ j := by
  have hM0 : M ≠ 0 := by
    rintro rfl
    norm_num at hM4
  have hKN : ℂ⟮K⟯ ≤ ℂ⟮M ^ 2⟯ := by
    have hK' : K = ((M ^ 2) ^ 2 + 1) / M ^ 2 := by
      field_simp
      linear_combination -hM4
    rw [adjoin_simple_le_iff, hK']
    have hNm := mem_adjoin_simple_self ℂ (M ^ 2)
    exact div_mem (add_mem (pow_mem hNm _) (one_mem _)) hNm
  have hNM : ℂ⟮M ^ 2⟯ ≤ ℂ⟮M⟯ := by
    rw [adjoin_simple_le_iff]
    exact pow_mem (mem_adjoin_simple_self ℂ M) _
  have h1 : relfinrank ℂ⟮K⟯ ℂ⟮M ^ 2⟯ = 1 ∨ relfinrank ℂ⟮K⟯ ℂ⟮M ^ 2⟯ = 2 := by
    have h := relfinrank_sup_adjoin_quadratic_twfNeg ℂ⟮K⟯ (M ^ 2)
      (p := X ^ 2 - C (AdjoinSimple.gen ℂ K) * X + 1) (by monicity!) (by compute_degree!) (by
        simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one,
          AdjoinSimple.algebraMap_gen]
        linear_combination hM4)
    rwa [sup_eq_right.mpr hKN] at h
  have h2 : relfinrank ℂ⟮M ^ 2⟯ ℂ⟮M⟯ = 1 ∨ relfinrank ℂ⟮M ^ 2⟯ ℂ⟮M⟯ = 2 := by
    have h := relfinrank_sup_adjoin_quadratic_twfNeg ℂ⟮M ^ 2⟯ M
      (p := X ^ 2 - C (AdjoinSimple.gen ℂ (M ^ 2))) (by monicity!) (by compute_degree!) (by
        simp only [map_sub, map_pow, aeval_X, aeval_C, AdjoinSimple.algebraMap_gen, sub_self])
    rwa [sup_eq_right.mpr hNM] at h
  refine ⟨hKN.trans hNM, ?_⟩
  rw [← relfinrank_mul_relfinrank hKN hNM]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2]
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- The trace parameter `z` has degree at least `2b - 1` over `ℂ(M)`. -/
theorem natDegree_minpoly_of_twistParamNeg {Ω : Type*} [Field Ω] [Algebra ℂ Ω] {b : ℕ}
    (hb : 1 ≤ b) {M K z : Ω} (hz : Transcendental ℂ z) (hM4 : M ^ 4 - K * M ^ 2 + 1 = 0)
    (hK : K = z - ((twfChebV z b - twfChebV z (b - 1)) * twfChebV z b)⁻¹)
    (hint : IsIntegral ℂ⟮M⟯ z) :
    2 * b - 1 ≤ (minpoly ℂ⟮M⟯ z).natDegree := by
  have hKz : ℂ⟮K⟯ ≤ ℂ⟮z⟯ := by
    rw [adjoin_simple_le_iff, hK]
    exact twistParamNeg_mem_adjoin_simple_twfNeg b z
  obtain ⟨hKM, j, hj⟩ := relfinrank_adjoin_pow_two_twfNeg hM4
  have e1 := relfinrank_mul_relfinrank hKz (le_sup_left : ℂ⟮z⟯ ≤ ℂ⟮z⟯ ⊔ ℂ⟮M⟯)
  have e2 := relfinrank_mul_relfinrank hKM (le_sup_right : ℂ⟮M⟯ ≤ ℂ⟮z⟯ ⊔ ℂ⟮M⟯)
  rw [relfinrank_adjoin_twistParamNegK hb hz hK] at e1
  have hr : relfinrank ℂ⟮M⟯ (ℂ⟮z⟯ ⊔ ℂ⟮M⟯) = (minpoly ℂ⟮M⟯ z).natDegree := by
    rw [sup_comm, relfinrank_sup_adjoin_simple_twfNeg, adjoin.finrank hint]
  rw [hr, hj] at e2
  have hdvd : 2 * b - 1 ∣ 2 ^ j * (minpoly ℂ⟮M⟯ z).natDegree := by
    rw [e2, ← e1]
    exact dvd_mul_right _ _
  have hodd : Odd (2 * b - 1) := ⟨b - 1, by omega⟩
  have hcop : Nat.Coprime (2 * b - 1) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hodd)
  exact Nat.le_of_dvd (minpoly.natDegree_pos hint) (hcop.dvd_of_dvd_mul_left hdvd)

/-- In a finite extension `Ω` of `ℂ(M)`, every `z` is integral over the image `ℂ⟮M⟯` of
`ℂ(M)`, of degree at most `[Ω : ℂ(M)]`. -/
private theorem natDegree_minpoly_adjoin_le_finrank_twfNeg {Ω : Type*} [Field Ω]
    [Algebra (RatFunc ℂ) Ω] [Algebra ℂ Ω] [IsScalarTower ℂ (RatFunc ℂ) Ω]
    [FiniteDimensional (RatFunc ℂ) Ω] (z : Ω) :
    IsIntegral ℂ⟮algebraMap (RatFunc ℂ) Ω RatFunc.X⟯ z ∧
      (minpoly ℂ⟮algebraMap (RatFunc ℂ) Ω RatFunc.X⟯ z).natDegree ≤
        Module.finrank (RatFunc ℂ) Ω := by
  set M := algebraMap (RatFunc ℂ) Ω RatFunc.X
  have hmem : ∀ a : RatFunc ℂ, algebraMap (RatFunc ℂ) Ω a ∈ ℂ⟮M⟯ := fun a ↦
    algHom_ratFunc_mem_adjoin_twfNeg (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) Ω) a
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

/-- An irreducible factor of `C_b` over `ℂ(M)` has degree at least `2b - 1`. -/
theorem natDegree_le_of_dvd_twistPolyNeg (b : ℕ) (hb : 1 ≤ b) {g : (RatFunc ℂ)[X]}
    (hg : Irreducible g)
    (hdvd : g ∣ (twistPolyNeg b).map
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))) :
    2 * b - 1 ≤ g.natDegree := by
  have hg0 : g ≠ 0 := hg.ne_zero
  have : Fact (Irreducible g) := ⟨hg⟩
  have : FiniteDimensional (RatFunc ℂ) (AdjoinRoot g) := (AdjoinRoot.powerBasis hg0).finite
  have hfin : Module.finrank (RatFunc ℂ) (AdjoinRoot g) = g.natDegree := by
    rw [(AdjoinRoot.powerBasis hg0).finrank, AdjoinRoot.powerBasis_dim]
  set M : AdjoinRoot g := algebraMap (RatFunc ℂ) (AdjoinRoot g) RatFunc.X with hMdef
  have hL : aeval (AdjoinRoot.root g) ((twistPolyNeg b).map
      ((algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ)))) = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  obtain ⟨-, -, hK⟩ := famParamNeg_inverse hb (famTKNeg_eq_zero_of_twistPolyNeg_root hb hL).2
  have hM0 : M ≠ 0 := by simp [M, RatFunc.X_ne_zero]
  have hM4 : M ^ 4 - famKQ (M ^ 2) * M ^ 2 + 1 = 0 := by
    simp only [famKQ]
    field_simp
    ring
  have hMtr : Transcendental ℂ M := by
    rw [hMdef, transcendental_algebraMap_iff (algebraMap (RatFunc ℂ) (AdjoinRoot g)).injective]
    exact RatFunc.transcendental_X
  have hz := transcendental_of_twistParamNeg_eq hMtr hM4 hK
  obtain ⟨hint, hle⟩ := natDegree_minpoly_adjoin_le_finrank_twfNeg (Ω := AdjoinRoot g)
    (famZK (famKQ (M ^ 2)) ((M ^ 2 * AdjoinRoot.root g + 1) / (AdjoinRoot.root g + M ^ 2)))
  exact ((natDegree_minpoly_of_twistParamNeg hb hz hM4 hK hint).trans hle).trans_eq hfin

end AJConjecture
