import Mathlib
import AJHandoff.TorusKnot.PairKAPolyHorizontal
import AJHandoff.TorusKnot.PairKRevCompanion
import AJHandoff.TorusKnot.PairKRevPattern
import AJHandoff.TorusKnot.PairKRevReduce
import AJHandoff.TorusKnot.PairKRevTuple
import AJHandoff.TorusKnot.PairKBmIdentity
import AJFamily.Quantum.TwistPolyIrreducible

/-!
# The reverse classical inclusion (follow-up priority 3; not needed for Theorem T)

The bound says that the curve of `Wh⁻₀(T(r, s))` lies in `(L - 1) B_m = 0`, `m = rs`. The
reverse inclusion says that every horizontal component of `B_m = 0` is attained: its zero set lies
in the Zariski closure of the eigenvalue set. Together they give, for every A-polynomial `A`,
the same horizontal irreducible factors for `A` and `(L - 1) B_m` (`aPolynomial_pair_factors`),
and, since `B_m` is irreducible over `ℂ(M)`, `A ≐ (L - 1) B_m` in `ℚ(M)[L, L⁻¹]`, where vertical
factors are units (`aPolynomial_pair_associated_famBound`); for `(2, 3)` this is the follow-up's
`A_S ≐ (L - 1) B_6`.

The reverse inclusion needs representations, i.e. the converse of the peripheral computation.
Its three inputs (crux, see `DESIGN.md`):

* `PairRealizesSatellite C K`: every pair of an `SL₂(ℂ)` representation `ψ` of the companion
  group and matrices `a, a₁` satisfying the pattern relations of `IsWhSatellite` comes from a
  representation of the knot group of `K` (for `pairWhiteheadKnot`: a tuple with all gap
  products `1`, built from `ψ, a, a₁` through the block list; the chamber products show that a
  tuple is fixed by the run of a block word exactly when all its gap products are `1`);
* pattern points: at every point `(M, L)` of a horizontal component of `B_m = 0` off a finite
  set, the normal form of `twist_normal_form_gen` can be solved backwards for `a, a₁` with
  `a₁ c^m = c^m a` and `c` non-scalar;
* companion points: for every `W ∈ SL₂(ℂ)` with trace off a finite set there is a nonabelian
  representation of the group of `T(r, s)` with `μ ↦ W` (explicit `A = diag(α, α⁻¹)`,
  `B = H diag(β, β⁻¹) H⁻¹`, one free parameter in `H`, trace of `μ = A^u B^v` non-constant).
-/

open Polynomial

namespace AJConjecture

/-- Every representation of the companion group together with matrices satisfying the pattern
relations of the Whitehead satellite structure comes from a representation of the knot group of
`K` with the prescribed meridian and pattern longitude. -/
def PairRealizesSatellite (C K : BraidKnot) : Prop :=
  ∀ (ψ : KnotGroup C →* Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (a a₁ : Matrix.SpecialLinearGroup (Fin 2) ℂ),
    ψ (meridian C) = compMer a a₁ → a₁ = (ψ (longitude C))⁻¹ * a * ψ (longitude C) →
      ∃ ρ : KnotGroup K →* Matrix.SpecialLinearGroup (Fin 2) ℂ, ρ (meridian K) = a ∧
        ρ (longitude K) = a ^ 2 * ψ (longitude C) * a⁻¹ * (ψ (longitude C))⁻¹ * a * a₁⁻¹ * a⁻¹

/-- The knot group of `Wh⁻₀(T(r, s))` realizes every pattern-and-companion representation. -/
theorem pairRealizesSatellite {r s : ℕ} (h : IsTorusPair r s) :
    PairRealizesSatellite (torusPairKnot r s h) (pairWhiteheadKnot r s h) := by
  intro ψ a a₁ hm ha₁
  subst ha₁
  obtain ⟨f, hfix, h0, hcomp⟩ := exists_pairFixedTuple h ψ a hm
  exact pairRealizes_of_fixedTuple h ψ a f hfix h0 hcomp

/-- Conjugating by `(z * w)⁻¹` with `z` central is conjugating by `w⁻¹`. -/
private theorem rev_conj_central {G : Type*} [Group G] (z w g : G)
    (hz : ∀ x : G, z * x = x * z) : (z * w)⁻¹ * g * (z * w) = w⁻¹ * g * w := by
  calc (z * w)⁻¹ * g * (z * w) = w⁻¹ * (z⁻¹ * (g * z)) * w := by group
    _ = w⁻¹ * (z⁻¹ * (z * g)) * w := by rw [hz]
    _ = w⁻¹ * g * w := by group

/-- Conjugating by `z * w` with `z` central is conjugating by `w`. -/
private theorem rev_conj_central' {G : Type*} [Group G] (z w g : G)
    (hz : ∀ x : G, z * x = x * z) : z * w * g * (z * w)⁻¹ = w * g * w⁻¹ := by
  calc z * w * g * (z * w)⁻¹ = z * (w * g * w⁻¹) * z⁻¹ := by group
    _ = w * g * w⁻¹ * z * z⁻¹ := by rw [hz]
    _ = w * g * w⁻¹ := by group

/-- Generic points of `B_(rs) = 0` are eigenvalue points: at a zero `(M, L)` of `B_(rs)` with
`M ≠ 0`, `M⁴ ≠ 1`, `M² + L ≠ 0`, pattern data (`exists_pattern_point`), a companion
representation (`exists_torusRep_meridian`) and the realization give a representation. -/
private theorem mem_eigenvalueSet_of_famB_zero {r s : ℕ} (h : IsTorusPair r s) {M L : ℂ}
    (hM : M ≠ 0) (hM4 : M ^ 4 ≠ 1) (hQ : M ^ 2 + L ≠ 0)
    (hB : evalPoint (mapC (famB (r * s))) (M, L) = 0) :
    (M, L) ∈ eigenvalueSet (pairWhiteheadKnot r s h) := by
  obtain ⟨a, a₁, ha10, ha00, hc01, hrel, hl10, hl00⟩ :=
    exists_pattern_point (r * s) (pair_mul_pos h) hM hM4 hQ hB
  set c := a * a₁⁻¹ * a⁻¹ * a₁ with hc
  obtain ⟨ψ, hψm, z, hz, hψl⟩ := exists_torusRep_meridian h c (Or.inr hc01)
  have hΛ : ψ (longitude _) = z * (c ^ (r * s))⁻¹ := by rw [hψl, zpow_neg, zpow_natCast]
  have ha₁ : a₁ = (ψ (longitude _))⁻¹ * a * ψ (longitude _) := by
    rw [hΛ, rev_conj_central z _ a hz, inv_inv]
    calc a₁ = a₁ * c ^ (r * s) * (c ^ (r * s))⁻¹ := by group
      _ = c ^ (r * s) * a * (c ^ (r * s))⁻¹ := by rw [hrel]
  obtain ⟨ρ, hρm, hρl⟩ := pairRealizesSatellite h ψ a a₁ hψm ha₁
  have hw : ρ (longitude _) = a ^ 2 * (c ^ (r * s))⁻¹ * a⁻¹ * c ^ (r * s) * a * a₁⁻¹ * a⁻¹ := by
    rw [hρl, hΛ]
    calc a ^ 2 * (z * (c ^ (r * s))⁻¹) * a⁻¹ * (z * (c ^ (r * s))⁻¹)⁻¹ * a * a₁⁻¹ * a⁻¹ =
        a ^ 2 * ((z * (c ^ (r * s))⁻¹) * a⁻¹ * (z * (c ^ (r * s))⁻¹)⁻¹) * a * a₁⁻¹ * a⁻¹ := by
          group
      _ = a ^ 2 * ((c ^ (r * s))⁻¹ * a⁻¹ * ((c ^ (r * s))⁻¹)⁻¹) * a * a₁⁻¹ * a⁻¹ := by
          rw [rev_conj_central' z _ a⁻¹ hz]
      _ = _ := by group
  exact ⟨ρ, by rw [hρm]; exact ha10, by rw [hw]; exact hl10, by rw [hρm]; exact ha00,
    by rw [hw]; exact hl00⟩

/-- Evaluation is multiplicative. -/
private theorem rev_evalPoint_mul (P Q : ℂ[X][X]) (p : ℂ × ℂ) :
    evalPoint (P * Q) p = evalPoint P p * evalPoint Q p := by
  simp [evalPoint, Polynomial.eval₂_mul]

/-- The homogenised Chebyshev sequence with `κ = 0` is a sequence of powers. -/
private theorem rev_homCheb_zero (τ : ℂ) (n : ℕ) : homCheb τ 0 (n + 1) = τ ^ n := by
  induction n with
  | zero => simp [homCheb]
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 from rfl, homCheb, ih]
    ring

/-- `B_m` does not vanish at `(M, L) = (2, -4)` (on the line `L = -M²` it is
`(M² (M⁴ - 1)²)^m`). -/
private theorem rev_famB_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    evalPoint (mapC (famB m)) (2, -4) ≠ 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [evalPoint_famB, evalPoint_famK, evalPoint_famTau, evalPoint_famA]
  norm_num
  rw [rev_homCheb_zero]
  exact pow_ne_zero _ (by norm_num)

/-- The polynomial `M (M⁴ - 1) (L + M²)` cutting out the excluded points. -/
private noncomputable def revBad : ℂ[X][X] := C (X * (X ^ 4 - 1)) * (X + C (X ^ 2))

private theorem evalPoint_revBad (M L : ℂ) :
    evalPoint revBad (M, L) = M * (M ^ 4 - 1) * (L + M ^ 2) := by
  simp [revBad, evalPoint, Polynomial.eval₂_pow]

/-- A horizontal irreducible factor of `B_m` does not divide `M (M⁴ - 1) (L + M²)`. -/
private theorem rev_not_dvd_revBad {m : ℕ} (hm : 1 ≤ m) {g : ℂ[X][X]} (hg : Irreducible g)
    (hdeg : 0 < g.natDegree) (hdvd : g ∣ mapC (famB m)) : ¬ g ∣ revBad := by
  intro hd
  have hq : (X * (X ^ 4 - 1) : ℂ[X]) ≠ 0 := by
    refine mul_ne_zero X_ne_zero fun h0 ↦ ?_
    have := congrArg (Polynomial.eval 2) h0
    norm_num at this
  rcases hg.prime.dvd_or_dvd hd with h1 | h1
  · have := Polynomial.natDegree_le_of_dvd h1 (C_ne_zero.2 hq)
    rw [natDegree_C] at this
    omega
  · obtain ⟨k, hk⟩ := h1
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      exact X_add_C_ne_zero _ hk
    have hd1 : (X + C (X ^ 2) : ℂ[X][X]).natDegree = 1 := natDegree_X_add_C _
    rw [hk, natDegree_mul hg.ne_zero hk0] at hd1
    have hkd : k.natDegree = 0 := by omega
    have hlc : g.leadingCoeff * k.leadingCoeff = 1 := by
      rw [← leadingCoeff_mul, ← hk]
      exact (monic_X_add_C _).leadingCoeff
    have hku : IsUnit k := by
      rw [eq_C_of_natDegree_eq_zero hkd]
      refine isUnit_C.2 (IsUnit.of_mul_eq_one_right g.leadingCoeff ?_)
      have hc0 : k.leadingCoeff = k.coeff 0 := by rw [leadingCoeff, hkd]
      rw [← hc0, hlc]
    have hℓg : (X + C (X ^ 2) : ℂ[X][X]) ∣ g := by
      rw [hk]
      exact (Associated.symm ⟨hku.unit, rfl⟩).dvd
    obtain ⟨u, hu⟩ := hℓg.trans hdvd
    apply rev_famB_ne_zero m hm
    rw [hu, rev_evalPoint_mul]
    simp [evalPoint, Polynomial.eval₂_pow]
    norm_num

/-- Reverse inclusion: every horizontal irreducible factor of `B_(rs)` over `ℂ` has its zero set
in the Zariski closure of the eigenvalue set of `Wh⁻₀(T(r, s))`. -/
theorem pair_reverse_inclusion {r s : ℕ} (h : IsTorusPair r s) {g : ℂ[X][X]}
    (hg : Irreducible g) (hdeg : 0 < g.natDegree) (hdvd : g ∣ mapC (famB (r * s))) :
    ∀ p : ℂ × ℂ, evalPoint g p = 0 →
      p ∈ zariskiClosure (eigenvalueSet (pairWhiteheadKnot r s h)) := by
  intro p hp P hP
  have hPℓ : g ∣ P * revBad := dvd_of_forall_evalPoint_eq_zero hg fun q hq ↦ by
    obtain ⟨M, L⟩ := q
    rw [rev_evalPoint_mul]
    by_cases hz : evalPoint revBad (M, L) = 0
    · rw [hz, mul_zero]
    rw [evalPoint_revBad] at hz
    have hM : M ≠ 0 := fun h0 ↦ hz (by rw [h0]; ring)
    have hM4 : M ^ 4 ≠ 1 := fun h0 ↦ hz (by rw [h0]; ring)
    have hQ : M ^ 2 + L ≠ 0 := fun h0 ↦ hz (by rw [add_comm L, h0]; ring)
    have hB : evalPoint (mapC (famB (r * s))) (M, L) = 0 := by
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, rev_evalPoint_mul, hq, zero_mul]
    rw [hP _ (mem_eigenvalueSet_of_famB_zero h hM hM4 hQ hB), zero_mul]
  rcases hg.prime.dvd_or_dvd hPℓ with h1 | h1
  · obtain ⟨k, rfl⟩ := h1
    rw [rev_evalPoint_mul, hp, zero_mul]
  · exact absurd h1 (rev_not_dvd_revBad (pair_mul_pos h) hg hdeg hdvd)

/-- An A-polynomial of `Wh⁻₀(T(r, s))` and `(L - 1) B_(rs)` have the same horizontal irreducible
factors over `ℂ`. -/
theorem aPolynomial_pair_factors {r s : ℕ} (h : IsTorusPair r s) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A) {g : ℂ[X][X]}
    (hg : Irreducible g) (hdeg : 0 < g.natDegree) :
    g ∣ mapC A ↔ g ∣ mapC (famBound (r * s)) := by
  constructor
  · intro hd
    have hz := (hA.2 g hg).1 hd
    exact dvd_of_forall_evalPoint_eq_zero hg fun p hp ↦
      hz p hp _ fun q hq ↦ evalPoint_famBound_pair h hq
  · intro hd
    have hsplit : mapC (famBound (r * s)) = (X - 1) * mapC (famB (r * s)) := by
      simp [famBound, mapC, Polynomial.map_mul]
    rw [hsplit] at hd
    rcases hg.prime.dvd_or_dvd hd with h1 | h1
    · exact h1.trans (sub_one_dvd_aPolynomial _ hA)
    · exact (hA.2 g hg).2 (pair_reverse_inclusion h hg hdeg h1)

/-- The map `ℤ[M][L] → ℂ(M)[L]` used to compare divisibility over the field `ℂ(M)`. -/
private noncomputable abbrev revToRatFunc : ℤ[X] →+* RatFunc ℂ :=
  (algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (Int.castRingHom ℂ))

/-- The map `ℤ[M] → ℂ(M)` is injective. -/
private theorem revToRatFunc_injective : Function.Injective revToRatFunc :=
  (IsFractionRing.injective ℂ[X] (RatFunc ℂ)).comp
    (Polynomial.map_injective _ (Int.cast_injective (α := ℂ)))

/-- For a torus pair, `rs ≥ 2`. -/
private theorem rev_two_le_mul {r s : ℕ} (h : IsTorusPair r s) : 2 ≤ r * s := by
  obtain ⟨hr, hrs, -⟩ := h
  nlinarith

/-- Divisibility in `ℂ(M)[L]` of two integer polynomials descends to the comparison ring
`ℚ(M)[L, L⁻¹]`: polynomial division over the field `ℚ(M)` is unchanged in `ℂ(M)`. -/
private theorem toComparison_dvd_of_ratFunc_dvd_rev {A B : ℤ[X][X]}
    (h : A.map revToRatFunc ∣ B.map revToRatFunc) : toComparison A ∣ toComparison B := by
  set ψ : ℤ[X] →+* RatFunc ℚ :=
    (algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)) with hψ
  set φ : ℚ[X] →+* RatFunc ℂ :=
    (algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (algebraMap ℚ ℂ)) with hφ
  have hφinj : Function.Injective φ :=
    (RatFunc.algebraMap_injective ℂ).comp
      (Polynomial.map_injective _ (algebraMap ℚ ℂ).injective)
  set ι : RatFunc ℚ →+* RatFunc ℂ := RatFunc.liftRingHom φ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφinj) with hι
  have hιX : ι (algebraMap ℚ[X] (RatFunc ℚ) X) = algebraMap ℂ[X] (RatFunc ℂ) X := by
    have hd := RatFunc.liftRingHom_apply_div φ
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφinj) X 1
    rw [map_one, div_one, map_one, div_one] at hd
    rw [hι, hd, hφ, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
  have hcomm : ι.comp ψ = revToRatFunc := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp only [eq_intCast, map_intCast]
    · simp only [RingHom.comp_apply, hψ, Polynomial.coe_mapRingHom, Polynomial.map_X, hιX,
        revToRatFunc]
  have hmap : ∀ P : ℤ[X][X], P.map revToRatFunc = (P.map ψ).map ι := by
    intro P
    rw [Polynomial.map_map, hcomm]
  rw [hmap, hmap, Polynomial.map_dvd_map'] at h
  exact map_dvd Polynomial.toLaurent h

/-- A polynomial of positive `L`-degree over `ℂ[M]` has an irreducible factor of positive
`L`-degree (an irreducible factor of its primitive part). -/
private theorem exists_irreducible_horizontal_factor_rev {P : ℂ[X][X]} (hP : 0 < P.natDegree) :
    ∃ g : ℂ[X][X], Irreducible g ∧ 0 < g.natDegree ∧ g ∣ P := by
  have hpd : P.primPart.natDegree = P.natDegree := natDegree_primPart P
  have hnu : ¬ IsUnit P.primPart := fun hu ↦ by
    have := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hnu (primPart_ne_zero P)
  refine ⟨g, hg, Nat.pos_of_ne_zero fun h0 ↦ hg.not_isUnit ?_, hgd.trans (primPart_dvd P)⟩
  have hgp : g.IsPrimitive := fun c hc ↦ isPrimitive_primPart P c (hc.trans hgd)
  rw [eq_C_of_natDegree_eq_zero h0] at hgp ⊢
  exact isUnit_C.2 (hgp _ dvd_rfl)

/-- Over `ℂ(M)`, `B_(rs)` divides every A-polynomial of `Wh⁻₀(T(r, s))`. -/
private theorem twistPoly_map_dvd_aPolynomial_rev {r s : ℕ} (h : IsTorusPair r s) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A) :
    (twistPoly (r * s)).map revToRatFunc ∣ A.map revToRatFunc := by
  have hm : 2 ≤ r * s := rev_two_le_mul h
  have hirr : Irreducible ((twistPoly (r * s)).map revToRatFunc) :=
    irreducible_twistPoly_ratFunc (r * s) hm
  have hinjC : Function.Injective (algebraMap ℂ[X] (RatFunc ℂ)) :=
    IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  have hBm : famB (r * s) = twistPoly (r * s) := famB_eq_twistPoly _ (by omega)
  have hdegC : 0 < (mapC (twistPoly (r * s))).natDegree := by
    rw [mapC, natDegree_map_eq_of_injective
      (Polynomial.map_injective _ (Int.cast_injective (α := ℂ))), natDegree_twistPoly]
    omega
  obtain ⟨g, hg, hgdeg, hgd⟩ := exists_irreducible_horizontal_factor_rev hdegC
  have hgA : g ∣ mapC A := (aPolynomial_pair_factors h hA hg hgdeg).2 <| hgd.trans <| by
    simp only [famBound, hBm, mapC, Polynomial.map_mul]
    exact dvd_mul_left _ _
  have hmapC : ∀ P : ℤ[X][X], (mapC P).map (algebraMap ℂ[X] (RatFunc ℂ)) =
      P.map revToRatFunc := fun P ↦ by rw [mapC, Polynomial.map_map]
  have hg' := Polynomial.map_dvd (algebraMap ℂ[X] (RatFunc ℂ)) hgd
  have hgA' := Polynomial.map_dvd (algebraMap ℂ[X] (RatFunc ℂ)) hgA
  rw [hmapC] at hg' hgA'
  obtain ⟨u, hu⟩ := hg'
  rcases hirr.isUnit_or_isUnit hu with h1 | h1
  · have := natDegree_eq_zero_of_isUnit h1
    rw [natDegree_map_eq_of_injective hinjC] at this
    omega
  · rw [hu]
    exact h1.mul_right_dvd.2 hgA'

/-- The classical equality in `R = ℚ(M)[L, L⁻¹]` (follow-up, priority 3): every A-polynomial of
`Wh⁻₀(T(r, s))` is associated to `(L - 1) B_(rs)`. Vertical factors (polynomials in `M` alone) are
units of `R`, so this is the paper's `A_K ≐ (L - 1) B_(rs)`; for `(2, 3)` it is `A ≐ (L - 1) B_6`. -/
theorem aPolynomial_pair_associated_famBound {r s : ℕ} (h : IsTorusPair r s) {A : ℤ[X][X]}
    (hA : IsAPolynomialOf (eigenvalueSet (pairWhiteheadKnot r s h)) A) :
    Associated (toComparison A) (toComparison (famBound (r * s))) := by
  refine associated_of_dvd_dvd (toComparison_dvd_famBound_pair h hA)
    (toComparison_dvd_of_ratFunc_dvd_rev ?_)
  have hm : 2 ≤ r * s := rev_two_le_mul h
  have hirr : Irreducible ((twistPoly (r * s)).map revToRatFunc) :=
    irreducible_twistPoly_ratFunc (r * s) hm
  have hlin : Irreducible ((X - 1 : ℤ[X][X]).map revToRatFunc) := by
    simpa using irreducible_X_sub_C (1 : RatFunc ℂ)
  have hsub : (X - 1 : ℤ[X][X]).map revToRatFunc ∣ A.map revToRatFunc := by
    have := Polynomial.map_dvd (algebraMap ℂ[X] (RatFunc ℂ)) (sub_one_dvd_aPolynomial _ hA)
    simpa [mapC, Polynomial.map_map] using this
  have htw := twistPoly_map_dvd_aPolynomial_rev h hA
  obtain ⟨a, ha⟩ := hsub
  rw [famBound, famB_eq_twistPoly _ (by omega), Polynomial.map_mul, ha]
  refine mul_dvd_mul_left _ ?_
  rw [ha] at htw
  rcases hirr.prime.dvd_or_dvd htw with h1 | h1
  · have hle := natDegree_le_of_dvd h1 hlin.ne_zero
    rw [natDegree_map_eq_of_injective revToRatFunc_injective, natDegree_twistPoly] at hle
    have h1d : ((X - 1 : ℤ[X][X]).map revToRatFunc).natDegree = 1 := by
      simpa using natDegree_X_sub_C (1 : RatFunc ℂ)
    omega
  · exact h1

end AJConjecture
