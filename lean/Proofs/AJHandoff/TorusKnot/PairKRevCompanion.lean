import Mathlib
import AJHandoff.TorusKnot.PairKTorusGroup

/-!
# Companion points: nonabelian representations of the group of `T(r, s)`

For every non-scalar `c ∈ SL₂(ℂ)` (an off-diagonal entry nonzero) there is a representation
`ψ` of the group of `T(r, s)` (Artin's presentation) with `ψ(μ) = c` and `ψ(λ) = z c^(-rs)`,
`z` central (`exists_torusRep_meridian`).

Route. For `cs = dr + 1`, elements `x, y` of a group with `x^r = y^s` central give the fixed
tuple `X_k = x^(-kc) (y^(-d) x^c) x^(kc)` (as in `knotGroup_torusPairKnot_equiv`), with
`X_0 = y^(-d) x^c` and `X_0 ⋯ X_(r-1) = y`, so `ψ(λ) = y^s X_0^(-rs)`. In `SL₂(ℂ)` take
`x = diag(α, α⁻¹)`, `y = H diag(β, β⁻¹) H⁻¹` with `α^r = β^s = -1`; the trace of `X_0` is affine
in a free parameter of `H` with nonzero slope, and two matrices of `SL₂(ℂ)` with equal trace and
nonzero `(1, 0)` entries are conjugate (by an explicit upper triangular matrix).
-/

namespace AJConjecture

section TorusTuple

variable {G : Type*} [Group G]

/-- The cyclic product `f_0 f_1 ⋯ f_(n-1)`, indices modulo `r`. -/
private def revCycProd {r : ℕ} (hr : 0 < r) (f : Fin r → G) (n : ℕ) : G :=
  ((List.range n).map fun t ↦ f ⟨t % r, Nat.mod_lt _ hr⟩).prod

private theorem revCycProd_succ {r : ℕ} (hr : 0 < r) (f : Fin r → G) (n : ℕ) :
    revCycProd hr f (n + 1) = revCycProd hr f n * f ⟨n % r, Nat.mod_lt _ hr⟩ := by
  simp only [revCycProd, List.range_succ, List.map_append, List.map_singleton, List.prod_append,
    List.prod_singleton]

/-- Conjugating by `a * z` with `z` central is conjugating by `a`. -/
private theorem revConj_mul_central {a b z : G} (hz : z ∈ Subgroup.center G) :
    (a * z)⁻¹ * b * (a * z) = a⁻¹ * b * a := by
  have := Subgroup.mem_center_iff.mp hz
  calc (a * z)⁻¹ * b * (a * z) = z⁻¹ * (a⁻¹ * b * a * z) := by group
    _ = z⁻¹ * (z * (a⁻¹ * b * a)) := by rw [this]
    _ = a⁻¹ * b * a := by group

/-- The images `x^(-kc) (y^(-d) x^c) x^(kc)` of the Artin generators. -/
def torusRevTuple (r : ℕ) (x y : G) (c d : ℕ) (k : Fin r) : G :=
  x ^ (-((k : ℤ) * c)) * (y ^ (-(d : ℤ)) * x ^ (c : ℤ)) * x ^ ((k : ℤ) * c)

private theorem torusRevTuple_mod {r : ℕ} (hr : 0 < r) {x : G} (y : G)
    (hx : x ^ r ∈ Subgroup.center G) (c d t : ℕ) :
    torusRevTuple r x y c d ⟨t % r, Nat.mod_lt _ hr⟩ =
      x ^ (-((t : ℤ) * c)) * (y ^ (-(d : ℤ)) * x ^ (c : ℤ)) * x ^ ((t : ℤ) * c) := by
  have hz : (x ^ r) ^ (((t / r : ℕ) : ℤ) * c) ∈ Subgroup.center _ :=
    Subgroup.zpow_mem _ hx _
  have e : x ^ ((t : ℤ) * c) =
      x ^ (((t % r : ℕ) : ℤ) * c) * (x ^ r) ^ (((t / r : ℕ) : ℤ) * c) := by
    rw [← zpow_natCast x r, ← zpow_mul, ← zpow_add]
    congr 1
    have h1 : ((t % r : ℕ) : ℤ) + (r : ℤ) * ((t / r : ℕ) : ℤ) = (t : ℤ) := by
      exact_mod_cast Nat.mod_add_div t r
    linear_combination (-(c : ℤ)) * h1
  simp only [torusRevTuple]
  rw [zpow_neg x ((t : ℤ) * c), e, revConj_mul_central hz, ← zpow_neg]

private theorem revCycProd_torusRevTuple {r : ℕ} (hr : 0 < r) {x : G} (y : G)
    (hx : x ^ r ∈ Subgroup.center G) (c d n : ℕ) :
    revCycProd hr (torusRevTuple r x y c d) n = y ^ (-((d : ℤ) * n)) * x ^ ((n : ℤ) * c) := by
  induction n with
  | zero => simp [revCycProd]
  | succ n ih =>
    rw [revCycProd_succ, ih, torusRevTuple_mod hr y hx]
    push_cast
    group

private theorem revCycProd_torusRevTuple_s {r s : ℕ} (hr : 0 < r) {x y : G}
    (hx : x ^ r ∈ Subgroup.center G) (hxy : x ^ r = y ^ s) {c d : ℕ}
    (hcd : c * s = d * r + 1) :
    revCycProd hr (torusRevTuple r x y c d) s = x := by
  rw [revCycProd_torusRevTuple hr y hx, show -((d : ℤ) * s) = (s : ℤ) * (-(d : ℤ)) by ring,
    zpow_mul, zpow_natCast, ← hxy, ← zpow_natCast x r, ← zpow_mul, ← zpow_add]
  conv_rhs => rw [← zpow_one x]
  congr 1
  have h1 : (c : ℤ) * s = d * r + 1 := by exact_mod_cast hcd
  linear_combination h1

private theorem revCycProd_torusRevTuple_r {r s : ℕ} (hr : 0 < r) {x y : G}
    (hx : x ^ r ∈ Subgroup.center G) (hxy : x ^ r = y ^ s) {c d : ℕ}
    (hcd : c * s = d * r + 1) :
    revCycProd hr (torusRevTuple r x y c d) r = y := by
  rw [revCycProd_torusRevTuple hr y hx, zpow_mul, zpow_natCast x r, hxy,
    ← zpow_natCast y s, ← zpow_mul, ← zpow_add]
  conv_rhs => rw [← zpow_one y]
  congr 1
  have h1 : (c : ℤ) * s = d * r + 1 := by exact_mod_cast hcd
  linear_combination h1

private theorem torusRevTuple_fixed {r s : ℕ} (hr : 0 < r) {x y : G}
    (hx : x ^ r ∈ Subgroup.center G) (hxy : x ^ r = y ^ s) {c d : ℕ}
    (hcd : c * s = d * r + 1) (k : Fin r) :
    revCycProd hr (torusRevTuple r x y c d) s *
        torusRevTuple r x y c d ⟨((k : ℕ) + s) % r, Nat.mod_lt _ hr⟩ *
        (revCycProd hr (torusRevTuple r x y c d) s)⁻¹ = torusRevTuple r x y c d k := by
  rw [revCycProd_torusRevTuple_s hr hx hxy hcd, torusRevTuple_mod hr y hx]
  have hz : (x ^ r) ^ (d : ℤ) ∈ Subgroup.center _ := Subgroup.zpow_mem _ hx _
  have e : x ^ ((((k : ℕ) + s : ℕ) : ℤ) * c) * x⁻¹ =
      x ^ ((k : ℤ) * c) * (x ^ r) ^ (d : ℤ) := by
    rw [← zpow_natCast x r, ← zpow_mul, ← zpow_neg_one, ← zpow_add, ← zpow_add]
    congr 1
    have h1 : (c : ℤ) * s = d * r + 1 := by exact_mod_cast hcd
    push_cast
    linear_combination h1
  have e2 : x * (x ^ (-((((k : ℕ) + s : ℕ) : ℤ) * c)) * (y ^ (-(d : ℤ)) * x ^ (c : ℤ)) *
      x ^ ((((k : ℕ) + s : ℕ) : ℤ) * c)) * x⁻¹ =
      (x ^ ((((k : ℕ) + s : ℕ) : ℤ) * c) * x⁻¹)⁻¹ * (y ^ (-(d : ℤ)) * x ^ (c : ℤ)) *
        (x ^ ((((k : ℕ) + s : ℕ) : ℤ) * c) * x⁻¹) := by
    group
  rw [e2, e, revConj_mul_central hz, ← zpow_neg, torusRevTuple]

/-- The braid relations hold for a tuple fixed by the braid. -/
private theorem revLift_artinRels_of_fixed (K : BraidKnot) (f : Fin K.strands → G)
    (hf : (braidRun K.strands K.word f).1 = f) :
    ∀ x ∈ artinRels K, FreeGroup.lift f x = 1 := by
  rintro _ ⟨k, rfl⟩
  rw [map_mul, map_inv, FreeGroup.lift_apply_of, map_mul, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one, lift_artinWord_snd, ← braidRun_fst_apply, hf]

/-- A representation of the group of `T(r, s)` from `x, y` with `x^r = y^s` central: the meridian
goes to `y^(-d) x^c` and the longitude to `y^s (y^(-d) x^c)^(-rs)`. -/
theorem exists_torusRep_of_pow_eq {r s : ℕ} (h : IsTorusPair r s) {x y : G}
    (hx : x ^ r ∈ Subgroup.center G) (hxy : x ^ r = y ^ s) {c d : ℕ}
    (hcd : c * s = d * r + 1) :
    ∃ ψ : KnotGroup (torusPairKnot r s h) →* G,
      ψ (meridian _) = y ^ (-(d : ℤ)) * x ^ (c : ℤ) ∧
        ψ (longitude _) = y ^ s * (y ^ (-(d : ℤ)) * x ^ (c : ℤ)) ^ (-((r * s : ℕ) : ℤ)) := by
  have hr : 0 < r := by have := h.1; omega
  have hfix : (braidRun r (torusPairWord r s) (torusRevTuple r x y c d)).1 =
      torusRevTuple r x y c d := funext fun k ↦
    (braidRun_torusPairWord_fst hr s (torusRevTuple r x y c d) k).trans
      (torusRevTuple_fixed hr hx hxy hcd k)
  let ψ : KnotGroup (torusPairKnot r s h) →* G :=
    PresentedGroup.toGroup (f := torusRevTuple r x y c d)
      (revLift_artinRels_of_fixed (torusPairKnot r s h) (torusRevTuple r x y c d) hfix)
  have hψ : ∀ k, ψ (PresentedGroup.of k) = torusRevTuple r x y c d k := fun k ↦
    PresentedGroup.toGroup.of _
  have hmer : ψ (meridian (torusPairKnot r s h)) = y ^ (-(d : ℤ)) * x ^ (c : ℤ) := by
    rw [meridian, hψ]
    simp [torusRevTuple]
  refine ⟨ψ, hmer, ?_⟩
  rw [longitude_torusPairKnot, map_mul, map_zpow, map_pow, hmer, torusFullProd, map_list_prod]
  have hprod : (List.map ψ (List.map (fun j : Fin r ↦
      (PresentedGroup.of j : KnotGroup (torusPairKnot r s h))) (List.finRange r))).prod = y := by
    rw [← revCycProd_torusRevTuple_r hr hx hxy hcd, revCycProd]
    congr 1
    refine List.ext_get (by simp) fun i h1 h2 ↦ ?_
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, List.getElem_finRange]
    simp only [List.length_map, List.length_finRange] at h1
    refine (hψ _).trans (congrArg _ (Fin.ext ?_))
    simp [Nat.mod_eq_of_lt h1]
  erw [hprod]

end TorusTuple

section SL2

open Matrix

/-- A root of `-1` of order exactly `2n`. -/
private theorem exists_root_neg_one (n : ℕ) (hn : 1 ≤ n) :
    ∃ ζ : ℂ, ζ ≠ 0 ∧ ζ ^ n = -1 ∧ ∀ k : ℕ, ζ ^ (2 * k) = 1 → n ∣ k := by
  have h2n : 2 * n ≠ 0 := by omega
  have hζ := Complex.isPrimitiveRoot_exp (2 * n) h2n
  set ζ := Complex.exp (2 * Real.pi * Complex.I / ((2 * n : ℕ) : ℂ))
  refine ⟨ζ, hζ.ne_zero h2n, ?_, fun k hk ↦ ?_⟩
  · have h := hζ.pow_of_dvd (p := n) (by omega) (Dvd.intro_left 2 rfl)
    rw [show 2 * n / n = 2 by rw [Nat.mul_div_cancel _ (by omega)]] at h
    exact h.eq_neg_one_of_two_right
  · have := (hζ.pow_eq_one_iff_dvd _).1 hk
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this

/-- The diagonal element `diag(u, u⁻¹)` of `SL₂(ℂ)`. -/
def revDiag (u : ℂˣ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![(u : ℂ), 0; 0, ((u⁻¹ : ℂˣ) : ℂ)], by simp [Matrix.det_fin_two]⟩

/-- `u ↦ diag(u, u⁻¹)` as a homomorphism. -/
def revDiagHom : ℂˣ →* Matrix.SpecialLinearGroup (Fin 2) ℂ where
  toFun := revDiag
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [revDiag]
  map_mul' u v := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [revDiag, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private theorem revDiagHom_coe (u : ℂˣ) :
    ((revDiagHom u : Matrix.SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(u : ℂ), 0; 0, (u : ℂ)⁻¹] := by
  change (revDiag u : Matrix (Fin 2) (Fin 2) ℂ) = _
  simp [revDiag]

/-- `diag(-1, -1)` is central. -/
private theorem revDiagHom_neg_one_mem_center :
    revDiagHom (-1) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℂ) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, revDiagHom_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Two elements of `SL₂(ℂ)` with the same trace and nonzero `(1, 0)` entries are conjugate. -/
private theorem exists_conj_of_trace_eq (X Y : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hX : X.1 1 0 ≠ 0) (hY : Y.1 1 0 ≠ 0) (htr : X.1 0 0 + X.1 1 1 = Y.1 0 0 + Y.1 1 1) :
    ∃ S : Matrix.SpecialLinearGroup (Fin 2) ℂ, S * X * S⁻¹ = Y := by
  set κ := Y.1 1 0 / X.1 1 0 with hκ
  have hκ0 : κ ≠ 0 := div_ne_zero hY hX
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_pow_nat_eq κ (by norm_num : 0 < 2)
  have hσ0 : σ ≠ 0 := by rintro rfl; simp at hσ; exact hκ0 hσ.symm
  set b := (Y.1 0 0 - X.1 0 0) / X.1 1 0 with hb
  have hdet : (!![σ⁻¹, σ⁻¹ * b; 0, σ⁻¹ * κ] : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
    simp only [Matrix.det_fin_two_of, mul_zero, sub_zero]
    rw [← hσ]
    field_simp
  let S : Matrix.SpecialLinearGroup (Fin 2) ℂ := ⟨_, hdet⟩
  refine ⟨S, mul_inv_eq_of_eq_mul ?_⟩
  have dX := X.det_coe
  have dY := Y.det_coe
  rw [Matrix.det_fin_two] at dX dY
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [S, Matrix.mul_apply, Fin.sum_univ_two, hκ, hb] <;> field_simp
  · ring
  · linear_combination (Y.1 0 0) * htr - dX + dY
  · linear_combination htr

/-- The element `H = [[1 + w, w], [1, 1]]` of `SL₂(ℂ)`. -/
private def revShear (w : ℂ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![1 + w, w; 1, 1], by simp [Matrix.det_fin_two]⟩

/-- The `(1, 0)` entry and the trace of `H diag(p, p⁻¹) H⁻¹ diag(q, q⁻¹)`. -/
private theorem revShear_conj_entries (w : ℂ) (p q : ℂˣ) :
    (revShear w * revDiagHom p * (revShear w)⁻¹ * revDiagHom q).1 1 0 =
        ((p : ℂ) - (p : ℂ)⁻¹) * q ∧
      (revShear w * revDiagHom p * (revShear w)⁻¹ * revDiagHom q).1 0 0 +
          (revShear w * revDiagHom p * (revShear w)⁻¹ * revDiagHom q).1 1 1 =
        (p : ℂ) * q + (p : ℂ)⁻¹ * (q : ℂ)⁻¹ +
          w * (((p : ℂ) - (p : ℂ)⁻¹) * ((q : ℂ) - (q : ℂ)⁻¹)) := by
  have hH : ((revShear w : Matrix.SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1 + w, w; 1, 1] := rfl
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    revDiagHom_coe, hH, Matrix.adjugate_fin_two_of]
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Trace is invariant under conjugation, in entries. -/
private theorem revTrace_conj (T c : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    (T * c * T⁻¹).1 0 0 + (T * c * T⁻¹).1 1 1 = c.1 0 0 + c.1 1 1 := by
  have dT := T.det_coe
  rw [Matrix.det_fin_two] at dT
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  linear_combination (c.1 0 0 + c.1 1 1) * dT

/-- A non-scalar element can be conjugated to have a nonzero `(1, 0)` entry. -/
private theorem exists_conj_entry_ne_zero (c : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hc : c.1 1 0 ≠ 0 ∨ c.1 0 1 ≠ 0) :
    ∃ T : Matrix.SpecialLinearGroup (Fin 2) ℂ, (T * c * T⁻¹).1 1 0 ≠ 0 := by
  rcases hc with hc | hc
  · exact ⟨1, by simpa using hc⟩
  · let J : Matrix.SpecialLinearGroup (Fin 2) ℂ := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
    refine ⟨J, ?_⟩
    have hJ : ((J : Matrix.SpecialLinearGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        !![0, 1; -1, 0] := rfl
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hJ,
      Matrix.adjugate_fin_two_of]
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] using hc

/-- Companion points: every non-scalar `c ∈ SL₂(ℂ)` is the image of the meridian under a
representation of the group of `T(r, s)` sending the longitude to a central element times
`c^(-rs)`. -/
theorem exists_torusRep_meridian {r s : ℕ} (h : IsTorusPair r s)
    (c : Matrix.SpecialLinearGroup (Fin 2) ℂ) (hc : c.1 1 0 ≠ 0 ∨ c.1 0 1 ≠ 0) :
    ∃ ψ : KnotGroup (torusPairKnot r s h) →* Matrix.SpecialLinearGroup (Fin 2) ℂ,
      ψ (meridian _) = c ∧ ∃ z : Matrix.SpecialLinearGroup (Fin 2) ℂ, (∀ g, z * g = g * z) ∧
        ψ (longitude _) = z * c ^ (-((r * s : ℕ) : ℤ)) := by
  obtain ⟨hr, hrs, hcop⟩ := h
  -- the Bezout exponents `c' s = d r + 1`
  obtain ⟨c', -, hc'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm (by omega)
  have hcd : c' * s = (s * c' / r) * r + 1 := by
    have := Nat.div_add_mod (s * c') r
    rw [hc'] at this
    linarith [Nat.mul_comm s c', Nat.mul_comm r (s * c' / r)]
  set d := s * c' / r
  obtain ⟨ζ, hζ0, hζr, hζo⟩ := exists_root_neg_one r (by omega)
  obtain ⟨η, hη0, hηs, hηo⟩ := exists_root_neg_one s (by omega)
  set α : ℂˣ := Units.mk0 ζ hζ0
  set β : ℂˣ := Units.mk0 η hη0
  set p : ℂˣ := β ^ (-(d : ℤ))
  set q : ℂˣ := α ^ c'
  have hp : (p : ℂ) - (p : ℂ)⁻¹ ≠ 0 := by
    intro h0
    have hp2 : (β : ℂ) ^ (2 * d) = 1 := by
      have hpne : (p : ℂ) ≠ 0 := p.ne_zero
      have : (p : ℂ) ^ 2 = 1 := by
        field_simp at h0
        linear_combination h0
      have hp' : (p : ℂ) = ((β : ℂ) ^ d)⁻¹ := by simp [p]
      rw [hp', inv_pow, inv_eq_one, ← pow_mul, Nat.mul_comm] at this
      exact this
    have hsd := hηo d (by simpa [β] using hp2)
    have : s ∣ c' * s := Dvd.intro_left c' rfl
    rw [hcd] at this
    have h1 : s ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_right hsd r)).1 this
    have := Nat.le_of_dvd one_pos h1
    omega
  have hq : (q : ℂ) - (q : ℂ)⁻¹ ≠ 0 := by
    intro h0
    have hq2 : (α : ℂ) ^ (2 * c') = 1 := by
      have hqne : (q : ℂ) ≠ 0 := q.ne_zero
      have : (q : ℂ) ^ 2 = 1 := by
        field_simp at h0
        linear_combination h0
      have hq' : (q : ℂ) = (α : ℂ) ^ c' := by simp [q]
      rw [hq', ← pow_mul, Nat.mul_comm] at this
      exact this
    have hrc := hζo c' (by simpa [α] using hq2)
    have : r ∣ c' * s := Dvd.dvd.mul_right hrc s
    rw [hcd] at this
    have h1 : r ∣ 1 := (Nat.dvd_add_right (Dvd.intro_left d rfl)).1 this
    have := Nat.le_of_dvd one_pos h1
    omega
  -- the target, with a nonzero `(1, 0)` entry
  obtain ⟨T, hT⟩ := exists_conj_entry_ne_zero c hc
  set τ := (T * c * T⁻¹).1 0 0 + (T * c * T⁻¹).1 1 1
  set w := (τ - ((p : ℂ) * q + (p : ℂ)⁻¹ * (q : ℂ)⁻¹)) /
    (((p : ℂ) - (p : ℂ)⁻¹) * ((q : ℂ) - (q : ℂ)⁻¹))
  set H := revShear w
  set x := revDiagHom α
  set y := H * revDiagHom β * H⁻¹
  set z : Matrix.SpecialLinearGroup (Fin 2) ℂ := revDiagHom (-1)
  have hzc := revDiagHom_neg_one_mem_center
  have hαr : α ^ r = -1 := Units.ext (by simp [α, hζr])
  have hβs : β ^ s = -1 := Units.ext (by simp [β, hηs])
  have hxr : x ^ r = z := by rw [← map_pow, hαr]
  have hys : y ^ s = z := by
    rw [conj_pow, ← map_pow, hβs]
    rw [Subgroup.mem_center_iff.mp hzc H, mul_inv_cancel_right]
  have hx : x ^ r ∈ Subgroup.center _ := hxr ▸ hzc
  obtain ⟨ψ₀, hψm, hψl⟩ := exists_torusRep_of_pow_eq ⟨hr, hrs, hcop⟩ hx (hxr.trans hys.symm) hcd
  have hX : y ^ (-(d : ℤ)) * x ^ (c' : ℤ) = H * revDiagHom p * H⁻¹ * revDiagHom q := by
    rw [conj_zpow, ← map_zpow, zpow_natCast, ← map_pow]
  obtain ⟨h10, htr⟩ := revShear_conj_entries w p q
  rw [← hX] at h10 htr
  have htr' : (y ^ (-(d : ℤ)) * x ^ (c' : ℤ)).1 0 0 +
      (y ^ (-(d : ℤ)) * x ^ (c' : ℤ)).1 1 1 = τ := by
    rw [htr, div_mul_cancel₀ _ (mul_ne_zero hp hq)]
    ring
  obtain ⟨S, hS⟩ := exists_conj_of_trace_eq _ _ (by rw [h10]; exact mul_ne_zero hp q.ne_zero) hT
    htr'
  set S' := T⁻¹ * S
  have hS' : S' * (y ^ (-(d : ℤ)) * x ^ (c' : ℤ)) * S'⁻¹ = c := by
    rw [_root_.mul_inv_rev, inv_inv]
    calc T⁻¹ * S * (y ^ (-(d : ℤ)) * x ^ (c' : ℤ)) * (S⁻¹ * T) =
        T⁻¹ * (S * (y ^ (-(d : ℤ)) * x ^ (c' : ℤ)) * S⁻¹) * T := by group
      _ = c := by rw [hS]; group
  refine ⟨(MulAut.conj S').toMonoidHom.comp ψ₀, ?_, z,
    fun g ↦ (Subgroup.mem_center_iff.mp hzc g).symm, ?_⟩
  · rw [MonoidHom.comp_apply, hψm, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hS']
  · rw [MonoidHom.comp_apply, hψl, MulEquiv.coe_toMonoidHom, map_mul, map_zpow]
    simp only [MulAut.conj_apply]
    rw [hS', hys, Subgroup.mem_center_iff.mp hzc S', mul_inv_cancel_right]

end SL2

end AJConjecture
