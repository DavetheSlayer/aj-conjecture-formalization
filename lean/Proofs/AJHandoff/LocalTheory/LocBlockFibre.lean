import Mathlib
import AJHandoff.LocalTheory.LocBlockAllocation

/-!
# The fibre `z = z₀` of a separating factorization at an allowed node

Let `β* P₀ = S* R*` be the content-free residual factorization at `z₀` (`R₀ = μ^a R*`,
`S₀ = μ^b S*`, `β*(z₀) ≠ 0`) of a factorization whose right factor contains the block `G = B g`
and whose left factor contains `H = B h`, at an allowed node `(z₀, λ)`. Then:

* the fibre of `R*` is `(u - λ) R^c` with `R^c` coprime to the fibre of `S*`, and `S*(z₀, λ) = 0`;
* the gradients are proportional: `∇R* = λ_R ∇G`, `∇S* = λ_S ∇H` at the node;
* `κ₁(z₀) λ_R λ_S = β*(z₀) κ₂(z₀) T(z₀, λ)`, `T = ∏_{i ≠ g, h} B_i`.

Proof. By `exists_locBlockAllocation`, `R*` and `S*` are, up to scalars which are units at `z₀`
(contents), the products of their blocks; on the fibre, `λ` is a simple root of `G`, no other
block of `R*` vanishes at `λ`, and a common root of `R^c` and the fibre of `S*` would be a meeting
point of two distinct blocks off `(G, H, λ)`, excluded by the whole-fibre condition.
Self-collisions inside one block are harmless because a block lies wholly in `R*` or in `S*`.
This replaces the library's `exists_nodeFibre_of_separating_collision`, whose hypothesis
`NodeCollisionFree` also demanded simple roots of the cofactor `T` on the fibre. The gradient
statements are the library's `exists_tangent_of_toComparison_dvd` over `ℂ(z)`, and the last
identity is `eval_derivative_mul_eq_of_mul_eq`.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- Evaluation at a point of the plane is evaluation of the fibre. -/
private theorem evalPoint_eq_eval_map_blockFibre (B : ℂ[X][X]) (z₀ l : ℂ) :
    evalPoint B (z₀, l) = (B.map (Polynomial.evalRingHom z₀)).eval l := by
  rw [evalPoint, eval_map]

/-- Evaluation at a point of a constant of `ℂ[z]`. -/
private theorem evalPoint_C_blockFibre (v : ℂ[X]) (p : ℂ × ℂ) :
    evalPoint (C v) p = v.eval p.1 := by
  rw [evalPoint, eval₂_C]
  rfl

/-- Evaluation at a point of a product. -/
private theorem evalPoint_mul_blockFibre (A B : ℂ[X][X]) (p : ℂ × ℂ) :
    evalPoint (A * B) p = evalPoint A p * evalPoint B p := by
  rw [evalPoint, eval₂_mul]
  rfl

/-- Evaluation at a point of a sum. -/
private theorem evalPoint_add_blockFibre (A B : ℂ[X][X]) (p : ℂ × ℂ) :
    evalPoint (A + B) p = evalPoint A p + evalPoint B p := by
  rw [evalPoint, eval₂_add]
  rfl

/-- Evaluation at a point of a finite product. -/
private theorem evalPoint_prod_blockFibre {ι : Type*} (s : Finset ι) (B : ι → ℂ[X][X])
    (p : ℂ × ℂ) : evalPoint (∏ i ∈ s, B i) p = ∏ i ∈ s, evalPoint (B i) p :=
  map_prod (Polynomial.eval₂RingHom (Polynomial.evalRingHom p.1) p.2) B s

/-- If `w₁ P = w₂ Q` with nonzero fibres at `z₀`, the scalars can be chosen nonvanishing at
`z₀`. -/
private theorem exists_C_mul_eq_eval_ne_zero_blockFibre {z₀ : ℂ} {w₁ w₂ : ℂ[X]} {P Q : ℂ[X][X]}
    (hw₁ : w₁ ≠ 0) (h : C w₁ * P = C w₂ * Q) (hP : P.map (Polynomial.evalRingHom z₀) ≠ 0)
    (hQ : Q.map (Polynomial.evalRingHom z₀) ≠ 0) :
    ∃ v₁ v₂ : ℂ[X], v₁.eval z₀ ≠ 0 ∧ v₂.eval z₀ ≠ 0 ∧ C v₁ * P = C v₂ * Q := by
  obtain ⟨a', b', c', hrel, rfl, rfl⟩ := UniqueFactorizationMonoid.exists_reduced_factors w₁ hw₁ w₂
  have hc : c' ≠ 0 := left_ne_zero_of_mul hw₁
  have h' : C a' * P = C b' * Q := by
    refine mul_left_cancel₀ (C_ne_zero.mpr hc) ?_
    rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, h]
  have hf := congrArg (Polynomial.map (Polynomial.evalRingHom z₀)) h'
  simp only [Polynomial.map_mul, Polynomial.map_C, coe_evalRingHom] at hf
  have hboth : ¬ (a'.eval z₀ = 0 ∧ b'.eval z₀ = 0) := by
    rintro ⟨ha, hb⟩
    exact not_isUnit_X_sub_C z₀ (hrel (dvd_iff_isRoot.mpr ha) (dvd_iff_isRoot.mpr hb))
  refine ⟨a', b', fun ha ↦ hboth ⟨ha, ?_⟩, fun hb ↦ hboth ⟨?_, hb⟩, h'⟩
  · rw [ha, C_0, zero_mul] at hf
    exact C_eq_zero.mp ((mul_eq_zero.mp hf.symm).resolve_right hQ)
  · rw [hb, C_0, zero_mul] at hf
    exact C_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hP)

/-- Divisibility over `ℂ(z)` is insensitive to a power of `z - z₀`. -/
private theorem locBlockDvd_of_eq_C_pow_mul_blockFibre {G R₀ Rs : ℂ[X][X]} {z₀ : ℂ} {a : ℕ}
    (hR : R₀ = C ((X - C z₀) ^ a) * Rs) (hG : LocBlockDvd G R₀) : LocBlockDvd G Rs := by
  have hinj : Function.Injective (algebraMap ℂ[X] (RatFunc ℂ)) :=
    IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  have hu : IsUnit (C (algebraMap ℂ[X] (RatFunc ℂ) ((X - C z₀) ^ a))) :=
    isUnit_C.mpr ((map_ne_zero_iff _ hinj).mpr (pow_ne_zero a (X_sub_C_ne_zero z₀))).isUnit
  unfold LocBlockDvd at hG ⊢
  rw [hR, Polynomial.map_mul, Polynomial.map_C] at hG
  exact hu.dvd_mul_left.mp hG

open Classical in
/-- The blocks split between the two primitive factors `R*`, `S*` of the residual
factorization, up to scalars that are units at `z₀`. -/
private theorem exists_locBlockSplit {P : LocOp} {ι : Type*} [Fintype ι]
    {B : ι → ℂ[X][X]} (hB : LocResidualBlocks P B) {κ₁ κ₂ : ℂ[X]} {g h : ι} {z₀ lam : ℂ}
    (hn : LocAllowedNode P B κ₁ κ₂ g h z₀ lam) {βs : ℂ[X]} {Ss Rs : ℂ[X][X]}
    (hRg : LocBlockDvd (B g) Rs) (hSh : LocBlockDvd (B h) Ss) (hβs : βs.eval z₀ ≠ 0)
    (hfac : C βs * opJet0 P = Ss * Rs) :
    ∃ A N : Finset ι, (∀ i, i ∈ A ↔ i ∉ N) ∧ g ∈ A ∧ h ∈ N ∧
      ∃ v₁ v₂ v₃ v₄ : ℂ[X], v₁.eval z₀ ≠ 0 ∧ v₂.eval z₀ ≠ 0 ∧ v₃.eval z₀ ≠ 0 ∧
        v₄.eval z₀ ≠ 0 ∧ C v₁ * Rs = C v₂ * ∏ i ∈ A, B i ∧
        C v₃ * Ss = C v₄ * ∏ i ∈ N, B i := by
  set φ := Polynomial.mapRingHom (Polynomial.evalRingHom z₀) with hφ
  have hP0f : (opJet0 P).map (Polynomial.evalRingHom z₀) ≠ 0 := by
    intro h0
    apply hn.lead_ne
    have hc := congrArg (fun q ↦ q.coeff (opJet0 P).natDegree) h0
    simpa only [coeff_map, coe_evalRingHom, coeff_zero, coeff_natDegree] using hc
  have hP0 : opJet0 P ≠ 0 := fun h0 ↦ hP0f (by rw [h0, Polynomial.map_zero])
  have hβs0 : βs ≠ 0 := fun h0 ↦ hβs (by rw [h0, eval_zero])
  have hprodf : (∏ i, B i).map (Polynomial.evalRingHom z₀) ≠ 0 := by
    have h1 := congrArg (Polynomial.map (Polynomial.evalRingHom z₀)) hn.sym
    simp only [Polynomial.map_mul, Polynomial.map_C, coe_evalRingHom] at h1
    intro h0
    rw [h0, mul_zero] at h1
    exact mul_ne_zero (C_ne_zero.mpr hn.κ₁_ne) hP0f h1
  have hSRf : (Ss * Rs).map (Polynomial.evalRingHom z₀) ≠ 0 := by
    rw [← hfac, Polynomial.map_mul, Polynomial.map_C, coe_evalRingHom]
    exact mul_ne_zero (C_ne_zero.mpr hβs) hP0f
  rw [Polynomial.map_mul] at hSRf
  obtain ⟨hdisj, w₁, w₂, w₃, w₄, hw₁, -, hw₃, -, hRw, hSw⟩ :=
    exists_locBlockAllocation hB hP0 hβs0 hfac
  have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i ↦ LocBlockDvd (B i) Rs) B
  rw [← hsplit, Polynomial.map_mul] at hprodf
  obtain ⟨v₁, v₂, hv₁, hv₂, hv⟩ :=
    exists_C_mul_eq_eval_ne_zero_blockFibre hw₁ hRw (right_ne_zero_of_mul hSRf)
      (left_ne_zero_of_mul hprodf)
  obtain ⟨v₃, v₄, hv₃, hv₄, hv'⟩ :=
    exists_C_mul_eq_eval_ne_zero_blockFibre hw₃ hSw (left_ne_zero_of_mul hSRf)
      (right_ne_zero_of_mul hprodf)
  refine ⟨_, _, fun i ↦ ?_, ?_, ?_, v₁, v₂, v₃, v₄, hv₁, hv₂, hv₃, hv₄, hv, hv'⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hRg
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun hR ↦ hdisj h hR hSh

/-- The fibre facts for one factor: if `v₁ R = v₂ ∏_{i ∈ A} B_i` with `g ∈ A`, then at a simple
root `λ` of `B g` on the fibre, `R` vanishes and its gradient is a multiple of `∇(B g)`. -/
private theorem evalPoint_gradient_blockFibre {ι : Type*} [DecidableEq ι] {B : ι → ℂ[X][X]}
    {A : Finset ι} {g : ι} (hg : g ∈ A) {z₀ lam : ℂ} {v₁ v₂ : ℂ[X]} {Rs : ℂ[X][X]} (hv₁ : v₁.eval z₀ ≠ 0)
    (hv : C v₁ * Rs = C v₂ * ∏ i ∈ A, B i) (hroot : evalPoint (B g) (z₀, lam) = 0) :
    evalPoint Rs (z₀, lam) = 0 ∧
      evalPoint (derivative Rs) (z₀, lam) =
        v₂.eval z₀ / v₁.eval z₀ * evalPoint (∏ i ∈ A.erase g, B i) (z₀, lam) *
          evalPoint (derivative (B g)) (z₀, lam) ∧
      evalPoint (innerDerivative Rs) (z₀, lam) =
        v₂.eval z₀ / v₁.eval z₀ * evalPoint (∏ i ∈ A.erase g, B i) (z₀, lam) *
          evalPoint (innerDerivative (B g)) (z₀, lam) := by
  rw [← Finset.mul_prod_erase A B hg] at hv
  set F := ∏ i ∈ A.erase g, B i
  have h0 := congrArg (fun q ↦ evalPoint q (z₀, lam)) hv
  have h1 := congrArg (fun q ↦ evalPoint (derivative q) (z₀, lam)) hv
  have h2 := congrArg (fun q ↦ evalPoint (innerDerivative q) (z₀, lam)) hv
  simp only [evalPoint_C_blockFibre, evalPoint_mul_blockFibre, hroot, zero_mul,
    mul_zero] at h0
  have hR0 : evalPoint Rs (z₀, lam) = 0 := (mul_eq_zero.mp h0).resolve_left hv₁
  simp only [derivative_mul, derivative_C, evalPoint_C_blockFibre, evalPoint_add_blockFibre,
    evalPoint_mul_blockFibre, hroot, zero_mul, zero_add, add_zero] at h1
  simp only [innerDerivative_mul, innerDerivative_C, evalPoint_C_blockFibre,
    evalPoint_add_blockFibre, evalPoint_mul_blockFibre, hroot, hR0, zero_mul, mul_zero,
    zero_add, add_zero] at h2
  refine ⟨hR0, ?_, ?_⟩
  · field_simp
    linear_combination h1
  · field_simp
    linear_combination h2

theorem exists_locNodeFibre {P : LocOp} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : ι → ℂ[X][X]} (hB : LocResidualBlocks P B) {κ₁ κ₂ : ℂ[X]} {g h : ι} {z₀ lam : ℂ}
    (hn : LocAllowedNode P B κ₁ κ₂ g h z₀ lam) {R₀ S₀ : ℂ[X][X]}
    (hRg : LocBlockDvd (B g) R₀) (hSh : LocBlockDvd (B h) S₀) {a b : ℕ} {βs : ℂ[X]}
    {Ss Rs : ℂ[X][X]} (hR : R₀ = C ((X - C z₀) ^ a) * Rs) (hS : S₀ = C ((X - C z₀) ^ b) * Ss)
    (hβs : βs.eval z₀ ≠ 0) (hfac : C βs * opJet0 P = Ss * Rs) :
    ∃ (Rc : ℂ[X]) (lR lS : ℂ), Rs.map (Polynomial.evalRingHom z₀) = (X - C lam) * Rc ∧
      (Ss.map (Polynomial.evalRingHom z₀)).eval lam = 0 ∧
      IsCoprime Rc (Ss.map (Polynomial.evalRingHom z₀)) ∧
      (derivative (Rs.map (Polynomial.evalRingHom z₀))).eval lam =
        lR * evalPoint (derivative (B g)) (z₀, lam) ∧
      ((innerDerivative Rs).map (Polynomial.evalRingHom z₀)).eval lam =
        lR * evalPoint (innerDerivative (B g)) (z₀, lam) ∧
      (derivative (Ss.map (Polynomial.evalRingHom z₀))).eval lam =
        lS * evalPoint (derivative (B h)) (z₀, lam) ∧
      ((innerDerivative Ss).map (Polynomial.evalRingHom z₀)).eval lam =
        lS * evalPoint (innerDerivative (B h)) (z₀, lam) ∧
      κ₁.eval z₀ * (lR * lS) =
        βs.eval z₀ * κ₂.eval z₀ * evalPoint (locCofactor B g h) (z₀, lam) := by
  have hRgs := locBlockDvd_of_eq_C_pow_mul_blockFibre hR hRg
  have hShs := locBlockDvd_of_eq_C_pow_mul_blockFibre hS hSh
  obtain ⟨A, N, hpart, hgA, hhN, v₁, v₂, v₃, v₄, hv₁, hv₂, hv₃, hv₄, hvR, hvS⟩ :=
    exists_locBlockSplit hB hn hRgs hShs hβs hfac
  obtain ⟨-, hRu, hRz⟩ := evalPoint_gradient_blockFibre hgA hv₁ hvR hn.root_g
  obtain ⟨hS0, hSu, hSz⟩ := evalPoint_gradient_blockFibre hhN hv₃ hvS hn.root_h
  set φ := Polynomial.evalRingHom z₀ with hφ
  set Qg := (B g).map φ /ₘ (X - C lam) with hQgdef
  have hQg : (X - C lam) * Qg = (B g).map φ := by
    refine mul_divByMonic_eq_iff_isRoot.mpr ?_
    rw [IsRoot, ← evalPoint_eq_eval_map_blockFibre]
    exact hn.root_g
  have hQgl : Qg.eval lam ≠ 0 := by
    have h1 := hn.du_g
    rw [evalPoint_eq_eval_map_blockFibre, ← derivative_map, ← hQg, derivative_mul] at h1
    simpa only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add,
      eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] using h1
  set F' := ∏ i ∈ A.erase g, B i with hF'
  set G' := ∏ i ∈ N.erase h, B i with hG'
  have hdisj : ∀ i j, i ∈ A → j ∈ N → i ≠ j := fun i j hi hj hij ↦
    (hpart i).mp hi (hij ▸ hj)
  have hhA : h ∉ A := fun hh ↦ (hpart h).mp hh hhN
  have hgN : g ∉ N := (hpart g).mp hgA
  refine ⟨C (v₂.eval z₀ / v₁.eval z₀) * Qg * F'.map φ,
    v₂.eval z₀ / v₁.eval z₀ * evalPoint F' (z₀, lam),
    v₄.eval z₀ / v₃.eval z₀ * evalPoint G' (z₀, lam), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the fibre of `R*` is `(u - λ) R^c`
    have hmapR := congrArg (Polynomial.map φ) hvR
    rw [← Finset.mul_prod_erase A B hgA] at hmapR
    simp only [Polynomial.map_mul, Polynomial.map_C, hφ, coe_evalRingHom] at hmapR
    have hc : C (v₁.eval z₀) * C (v₂.eval z₀ / v₁.eval z₀) = C (v₂.eval z₀) := by
      rw [← C_mul, mul_div_cancel₀ _ hv₁]
    refine mul_left_cancel₀ (C_ne_zero.mpr hv₁) ?_
    linear_combination hmapR - (C (v₂.eval z₀) * F'.map φ) * hQg -
      ((X - C lam) * Qg * F'.map φ) * hc
  · rw [← evalPoint_eq_eval_map_blockFibre]
    exact hS0
  · -- `R^c` and the fibre of `S*` have no common root
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
    intro l
    simp only [coe_aeval_eq_eval]
    by_contra hcon
    push Not at hcon
    obtain ⟨hRc, hSl⟩ := hcon
    rw [← evalPoint_eq_eval_map_blockFibre] at hSl
    have hSl' := congrArg (fun q ↦ evalPoint q (z₀, l)) hvS
    simp only [evalPoint_mul_blockFibre, evalPoint_C_blockFibre, evalPoint_prod_blockFibre,
      hSl, mul_zero] at hSl'
    obtain ⟨j, hjN, hj⟩ :=
      Finset.prod_eq_zero_iff.mp ((mul_eq_zero.mp hSl'.symm).resolve_left hv₄)
    simp only [eval_mul, eval_C] at hRc
    rcases mul_eq_zero.mp hRc with hRc | hRc
    · rcases mul_eq_zero.mp hRc with hRc | hRc
      · exact div_ne_zero hv₂ hv₁ hRc
      · have hgl : evalPoint (B g) (z₀, l) = 0 := by
          rw [evalPoint_eq_eval_map_blockFibre, ← hQg, eval_mul, hRc, mul_zero]
        obtain ⟨rfl, -⟩ := hn.fibre g j (hdisj g j hgA hjN) l hgl hj
        exact hQgl hRc
    · rw [hφ, ← evalPoint_eq_eval_map_blockFibre, hF', evalPoint_prod_blockFibre] at hRc
      obtain ⟨i, hiA, hi⟩ := Finset.prod_eq_zero_iff.mp hRc
      obtain ⟨-, hc⟩ := hn.fibre i j (hdisj i j (Finset.mem_of_mem_erase hiA) hjN) l hi hj
      rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Finset.ne_of_mem_erase hiA rfl
      · exact hhA (Finset.mem_of_mem_erase hiA)
  · rw [derivative_map, ← evalPoint_eq_eval_map_blockFibre, hRu]
  · rw [← evalPoint_eq_eval_map_blockFibre, hRz]
  · rw [derivative_map, ← evalPoint_eq_eval_map_blockFibre, hSu]
  · rw [← evalPoint_eq_eval_map_blockFibre, hSz]
  · -- the scalar identity
    have hAN : Disjoint A N :=
      Finset.disjoint_left.mpr fun i hiA hiN ↦ hdisj i i hiA hiN rfl
    have hT : locCofactor B g h = F' * G' := by
      rw [locCofactor, hF', hG', ← Finset.prod_union (Finset.disjoint_of_subset_left
        (Finset.erase_subset g A) (Finset.disjoint_of_subset_right (Finset.erase_subset h N) hAN))]
      refine Finset.prod_congr (Finset.ext fun i ↦ ?_) fun _ _ ↦ rfl
      simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_union, and_true]
      constructor
      · rintro ⟨hih, hig⟩
        by_cases hiA : i ∈ A
        · exact Or.inl ⟨hig, hiA⟩
        · exact Or.inr ⟨hih, not_not.mp fun hiN ↦ hiA ((hpart i).mpr hiN)⟩
      · rintro (⟨hig, hiA⟩ | ⟨hih, hiN⟩)
        · exact ⟨fun hi ↦ hhA (hi ▸ hiA), hig⟩
        · exact ⟨hih, fun hi ↦ hgN (hi ▸ hiN)⟩
    have hsplit : ∏ i, B i = (∏ i ∈ A, B i) * ∏ i ∈ N, B i := by
      rw [← Finset.prod_union hAN]
      refine Finset.prod_congr (Finset.ext fun i ↦ ?_) fun _ _ ↦ rfl
      simp only [Finset.mem_univ, Finset.mem_union, true_iff]
      by_cases hiA : i ∈ A
      · exact Or.inl hiA
      · exact Or.inr (not_not.mp fun hiN ↦ hiA ((hpart i).mpr hiN))
    have hP0 : opJet0 P ≠ 0 := fun h0 ↦ hn.lead_ne (by rw [h0, leadingCoeff_zero, eval_zero])
    have hκ₁ : κ₁ ≠ 0 := fun h0 ↦ hn.κ₁_ne (by rw [h0, eval_zero])
    have hprod : ∏ i, B i ≠ 0 := by
      intro h0
      have h1 := hn.sym
      rw [h0, mul_zero] at h1
      exact mul_ne_zero (C_ne_zero.mpr hκ₁) hP0 h1
    have hpoly : C (κ₁ * v₂ * v₄) * ∏ i, B i = C (βs * κ₂ * v₁ * v₃) * ∏ i, B i := by
      simp only [C_mul]
      linear_combination (C κ₁ * C v₂ * C v₄) * hsplit -
        (C κ₁ * C v₄ * ∏ i ∈ N, B i) * hvR - (C κ₁ * C v₁ * Rs) * hvS -
        (C v₁ * C v₃ * C κ₁) * hfac + (C v₁ * C v₃ * C βs) * hn.sym
    have hval := congrArg (eval z₀) (C_injective (mul_right_cancel₀ hprod hpoly))
    simp only [eval_mul] at hval
    rw [hT, evalPoint_mul_blockFibre]
    field_simp
    linear_combination (evalPoint F' (z₀, lam) * evalPoint G' (z₀, lam)) * hval

end AJConjecture
