import Mathlib
import AJFamily.MarkovEquiv
import AJHandoff.TorusKnot.PairKCoprodTorsion
import AJHandoff.TorusKnot.PairKKnot

/-!
# T-DIST (b): distinctness through the JSJ decomposition, conditional

The topological part of the source argument (classical note §6) is not formalized:
`WhiteheadJSJProp` states its consequence for the knot groups. For prime knots, isomorphic knot
groups give homeomorphic exteriors up to orientation (Gordon–Luecke, Whitten); the canonical
torus decomposition (Hatcher, Theorem 1.9) of the exterior of `Wh(T(r, s))` has the
Whitehead-link piece and the small Seifert piece `D²(r, s)`, so a homeomorphism of exteriors
restricts to the companion exteriors and induces an isomorphism of the companion groups.

Formal part: Markov equivalent closed braids have isomorphic knot groups (the easy direction of
Markov's theorem: every `MarkovStep` gives an isomorphism of Artin presentations,
`knotGroup_equiv_of_markovEquiv`); companion groups of different admissible pairs are not
isomorphic (centre, quotient `C_r * C_s`, torsion orders: `PairKCoprodTorsion`). Hence, given
`WhiteheadJSJProp`, different pairs give closed braids that are not Markov equivalent
(`pairWhiteheadKnot_not_markovEquiv_of_jsj`). The unconditional formal distinctness is T-DIST (a)
(`AJHandoff.TorusKnot.PairKDistinct`).
-/

namespace AJConjecture

/-! ### Artin's action as an endomorphism of the free group -/

/-- Artin's action of a braid word as an endomorphism of the free group (the head letter acts
last). -/
private def artinAct (m : ℕ) (w : BraidWord) : FreeGroup (Fin m) →* FreeGroup (Fin m) :=
  w.foldr (fun g φ ↦ (artinHom m g).comp φ) (MonoidHom.id _)

private theorem artinAct_cons (m : ℕ) (g : ℕ × Bool) (w : BraidWord) :
    artinAct m (g :: w) = (artinHom m g).comp (artinAct m w) := rfl

private theorem artinAct_append (m : ℕ) (u v : BraidWord) :
    artinAct m (u ++ v) = (artinAct m u).comp (artinAct m v) := by
  induction u with
  | nil => rfl
  | cons g u ih => rw [List.cons_append, artinAct_cons, artinAct_cons, ih, MonoidHom.comp_assoc]

private theorem artinHom_of_markov (m : ℕ) (g : ℕ × Bool) (k : Fin m) :
    artinHom m g (FreeGroup.of k) = (artinGen m g k).2 * FreeGroup.of (artinGen m g k).1 *
      ((artinGen m g k).2)⁻¹ := by
  simp [artinHom]

/-- The conjugate `c_k x_(p(k)) c_k⁻¹` of Artin's presentation is the action of the word on
`x_k`. -/
private theorem artinWord_conj_eq_artinAct (m : ℕ) (w : BraidWord) (k : Fin m) :
    (artinWord m w k).2 * FreeGroup.of (artinWord m w k).1 * ((artinWord m w k).2)⁻¹ =
      artinAct m w (FreeGroup.of k) := by
  induction w with
  | nil => simp [artinWord, artinAct]
  | cons g w ih =>
    rw [artinAct_cons, MonoidHom.comp_apply, ← ih]
    simp only [artinWord, map_mul, map_inv, artinHom_of_markov]
    group

/-- The relators `x_k⁻¹ φ(x_k)` of the presentation of the fixed points of an endomorphism. -/
private def endRels {m : ℕ} (φ : FreeGroup (Fin m) →* FreeGroup (Fin m)) :
    Set (FreeGroup (Fin m)) :=
  {r | ∃ k : Fin m, r = (FreeGroup.of k)⁻¹ * φ (FreeGroup.of k)}

private theorem artinRels_eq_endRels (K : BraidKnot) :
    artinRels K = endRels (artinAct K.strands K.word) := by
  ext r
  simp only [artinRels, endRels, Set.mem_ofPred_eq, artinWord_conj_eq_artinAct]

/-- Modulo its relators, `φ` acts trivially. -/
private theorem mk_endRels_map {m : ℕ} (φ : FreeGroup (Fin m) →* FreeGroup (Fin m))
    (y : FreeGroup (Fin m)) :
    PresentedGroup.mk (endRels φ) (φ y) = PresentedGroup.mk (endRels φ) y := by
  have h : (PresentedGroup.mk (endRels φ)).comp φ = PresentedGroup.mk (endRels φ) := by
    refine FreeGroup.ext_hom _ _ fun k ↦ ?_
    have hmem : (FreeGroup.of k)⁻¹ * φ (FreeGroup.of k) ∈ endRels φ := ⟨k, rfl⟩
    have h1 := PresentedGroup.one_of_mem hmem
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  exact DFunLike.congr_fun h y

/-- Conjugate endomorphisms have isomorphic presentations. -/
private theorem nonempty_mulEquiv_endRels_of_conj {m : ℕ}
    {φ₁ φ₂ θ θ' : FreeGroup (Fin m) →* FreeGroup (Fin m)}
    (h1 : θ'.comp θ = MonoidHom.id _) (h2 : θ.comp θ' = MonoidHom.id _)
    (hc : φ₁.comp θ = θ.comp φ₂) :
    Nonempty (PresentedGroup (endRels φ₁) ≃* PresentedGroup (endRels φ₂)) := by
  have hc' : θ'.comp φ₁ = φ₂.comp θ' := by
    calc θ'.comp φ₁ = θ'.comp (φ₁.comp (θ.comp θ')) := by rw [h2, MonoidHom.comp_id]
      _ = θ'.comp ((θ.comp φ₂).comp θ') := by rw [← hc]; rfl
      _ = (θ'.comp θ).comp (φ₂.comp θ') := rfl
      _ = φ₂.comp θ' := by rw [h1, MonoidHom.id_comp]
  let Φ : PresentedGroup (endRels φ₂) →* PresentedGroup (endRels φ₁) :=
    PresentedGroup.toGroup (f := fun k ↦ PresentedGroup.mk (endRels φ₁) (θ (FreeGroup.of k)))
      (by
        rintro _ ⟨k, rfl⟩
        have hl : ∀ x, FreeGroup.lift (fun k ↦ PresentedGroup.mk (endRels φ₁)
            (θ (FreeGroup.of k))) x = PresentedGroup.mk (endRels φ₁) (θ x) := by
          intro x
          have : FreeGroup.lift (fun k ↦ PresentedGroup.mk (endRels φ₁) (θ (FreeGroup.of k))) =
              (PresentedGroup.mk (endRels φ₁)).comp θ := FreeGroup.ext_hom _ _ fun k ↦ by simp
          rw [this, MonoidHom.comp_apply]
        rw [hl, map_mul, map_inv, map_mul, map_inv, ← MonoidHom.comp_apply θ φ₂, ← hc,
          MonoidHom.comp_apply, mk_endRels_map, inv_mul_cancel])
  let Ψ : PresentedGroup (endRels φ₁) →* PresentedGroup (endRels φ₂) :=
    PresentedGroup.toGroup (f := fun k ↦ PresentedGroup.mk (endRels φ₂) (θ' (FreeGroup.of k)))
      (by
        rintro _ ⟨k, rfl⟩
        have hl : ∀ x, FreeGroup.lift (fun k ↦ PresentedGroup.mk (endRels φ₂)
            (θ' (FreeGroup.of k))) x = PresentedGroup.mk (endRels φ₂) (θ' x) := by
          intro x
          have : FreeGroup.lift (fun k ↦ PresentedGroup.mk (endRels φ₂) (θ' (FreeGroup.of k))) =
              (PresentedGroup.mk (endRels φ₂)).comp θ' := FreeGroup.ext_hom _ _ fun k ↦ by simp
          rw [this, MonoidHom.comp_apply]
        rw [hl, map_mul, map_inv, map_mul, map_inv, ← MonoidHom.comp_apply θ' φ₁, hc',
          MonoidHom.comp_apply, mk_endRels_map, inv_mul_cancel])
  have hΦ : ∀ x, Φ (PresentedGroup.mk _ x) = PresentedGroup.mk _ (θ x) := by
    intro x
    have : Φ.comp (PresentedGroup.mk _) = (PresentedGroup.mk (endRels φ₁)).comp θ := by
      refine FreeGroup.ext_hom _ _ fun k ↦ ?_
      change Φ (PresentedGroup.of k) = _
      simp only [Φ, PresentedGroup.toGroup.of, MonoidHom.comp_apply]
    exact DFunLike.congr_fun this x
  have hΨ : ∀ x, Ψ (PresentedGroup.mk _ x) = PresentedGroup.mk _ (θ' x) := by
    intro x
    have : Ψ.comp (PresentedGroup.mk _) = (PresentedGroup.mk (endRels φ₂)).comp θ' := by
      refine FreeGroup.ext_hom _ _ fun k ↦ ?_
      change Ψ (PresentedGroup.of k) = _
      simp only [Ψ, PresentedGroup.toGroup.of, MonoidHom.comp_apply]
    exact DFunLike.congr_fun this x
  refine ⟨MonoidHom.toMulEquiv Ψ Φ (PresentedGroup.ext fun k ↦ ?_)
    (PresentedGroup.ext fun k ↦ ?_)⟩
  · change Φ (Ψ (PresentedGroup.mk _ (FreeGroup.of k))) = PresentedGroup.mk _ (FreeGroup.of k)
    rw [hΨ, hΦ, ← MonoidHom.comp_apply θ θ', h2, MonoidHom.id_apply]
  · change Ψ (Φ (PresentedGroup.mk _ (FreeGroup.of k))) = PresentedGroup.mk _ (FreeGroup.of k)
    rw [hΦ, hΨ, ← MonoidHom.comp_apply θ' θ, h1, MonoidHom.id_apply]


/-- The JSJ input, stated as its consequence for the knot groups of these closed braids: an
isomorphism of the knot groups of two doubles gives an isomorphism of the companion groups. It is
not a single literature theorem: it bundles (i) that the Artin group `KnotGroup` of the closed
braid is the fundamental group of the knot exterior, (ii) the identification of
`pairWhiteheadKnot r s h` with the satellite `Wh(T(r, s))` (interpretation, see `AJHandoff`),
(iii) Gordon–Luecke and Whitten (isomorphic groups of prime knots give homeomorphic exteriors),
and (iv) uniqueness of the JSJ decomposition (Hatcher, Theorem 1.9), so that a homeomorphism of
exteriors restricts to the companion exteriors. -/
def WhiteheadJSJProp : Prop :=
  ∀ (r s r' s' : ℕ) (h : IsTorusPair r s) (h' : IsTorusPair r' s'),
    Nonempty (KnotGroup (pairWhiteheadKnot r s h) ≃* KnotGroup (pairWhiteheadKnot r' s' h')) →
      Nonempty (KnotGroup (torusPairKnot r s h) ≃* KnotGroup (torusPairKnot r' s' h'))

/-! ### One letter on the generators -/

private theorem artinHom_mk_self {m i : ℕ} (h : i + 1 < m) (b : Bool) (hi : i < m) :
    artinHom m (i, b) (FreeGroup.of ⟨i, hi⟩) =
      if b then FreeGroup.of ⟨i, hi⟩ * FreeGroup.of ⟨i + 1, h⟩ * (FreeGroup.of ⟨i, hi⟩)⁻¹
      else FreeGroup.of ⟨i + 1, h⟩ := by
  cases b <;> simp [artinHom_of_markov, artinGen, h]

private theorem artinHom_mk_succ {m i : ℕ} (h : i + 1 < m) (b : Bool) :
    artinHom m (i, b) (FreeGroup.of ⟨i + 1, h⟩) =
      if b then FreeGroup.of ⟨i, by omega⟩
      else (FreeGroup.of ⟨i + 1, h⟩)⁻¹ * FreeGroup.of ⟨i, by omega⟩ *
        FreeGroup.of ⟨i + 1, h⟩ := by
  cases b <;> simp [artinHom_of_markov, artinGen, h]

private theorem artinHom_mk_ne {m i : ℕ} (b : Bool) (j : ℕ) (hj : j < m) (h1 : j ≠ i)
    (h2 : j ≠ i + 1) : artinHom m (i, b) (FreeGroup.of ⟨j, hj⟩) = FreeGroup.of ⟨j, hj⟩ := by
  by_cases h : i + 1 < m <;> simp [artinHom_of_markov, artinGen, h, h1, h2]

private theorem artinHom_of_not_lt {m i : ℕ} (h : ¬ i + 1 < m) (b : Bool) :
    artinHom m (i, b) = MonoidHom.id _ :=
  FreeGroup.ext_hom _ _ fun k ↦ by simp [artinHom_of_markov, artinGen, h]

set_option linter.unusedSimpArgs false in
/-- `σ_i^{±1} σ_i^{∓1}` acts trivially. -/
private theorem artinHom_comp_not {m i : ℕ} (h : i + 1 < m) (b : Bool) :
    (artinHom m (i, b)).comp (artinHom m (i, !b)) = MonoidHom.id _ := by
  refine FreeGroup.ext_hom _ _ fun k ↦ ?_
  obtain ⟨k, hk⟩ := k
  rw [MonoidHom.comp_apply, MonoidHom.id_apply]
  rcases (by omega : k = i ∨ k = i + 1 ∨ (k ≠ i ∧ k ≠ i + 1)) with rfl | rfl | ⟨h1, h2⟩
  · cases b
    · simp (disch := omega) [artinHom_mk_self h, artinHom_mk_succ h]
      group
    · simp (disch := omega) [artinHom_mk_self h, artinHom_mk_succ h]
  · cases b
    · simp (disch := omega) [artinHom_mk_self h, artinHom_mk_succ h]
    · simp (disch := omega) [artinHom_mk_self h, artinHom_mk_succ h]
      group
  · simp (disch := omega) [artinHom_mk_ne]

set_option linter.unusedSimpArgs false in
/-- Generators at distance at least two commute. -/
private theorem artinHom_comm {m i j : ℕ} (b c : Bool) (hij : i + 2 ≤ j) (h : j + 1 < m) :
    (artinHom m (i, b)).comp (artinHom m (j, c)) =
      (artinHom m (j, c)).comp (artinHom m (i, b)) := by
  have hi : i + 1 < m := by omega
  refine FreeGroup.ext_hom _ _ fun k ↦ ?_
  obtain ⟨k, hk⟩ := k
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  rcases (by omega : k = i ∨ k = i + 1 ∨ k = j ∨ k = j + 1 ∨
      (k ≠ i ∧ k ≠ i + 1 ∧ k ≠ j ∧ k ≠ j + 1)) with rfl | rfl | rfl | rfl | ⟨h1, h2, h3, h4⟩
  · cases b <;> cases c <;>
      simp (disch := omega) [artinHom_mk_self hi, artinHom_mk_succ hi, artinHom_mk_self h,
        artinHom_mk_succ h, artinHom_mk_ne]
  · cases b <;> cases c <;>
      simp (disch := omega) [artinHom_mk_self hi, artinHom_mk_succ hi, artinHom_mk_self h,
        artinHom_mk_succ h, artinHom_mk_ne]
  · cases b <;> cases c <;>
      simp (disch := omega) [artinHom_mk_self hi, artinHom_mk_succ hi, artinHom_mk_self h,
        artinHom_mk_succ h, artinHom_mk_ne]
  · cases b <;> cases c <;>
      simp (disch := omega) [artinHom_mk_self hi, artinHom_mk_succ hi, artinHom_mk_self h,
        artinHom_mk_succ h, artinHom_mk_ne]
  · simp (disch := omega) [artinHom_mk_ne]

set_option linter.unusedSimpArgs false in
/-- The braid relation `σ_i σ_{i+1} σ_i = σ_{i+1} σ_i σ_{i+1}` holds for Artin's action. -/
private theorem artinHom_braid {m i : ℕ} (h : i + 2 < m) :
    (artinHom m (i, true)).comp ((artinHom m (i + 1, true)).comp (artinHom m (i, true))) =
      (artinHom m (i + 1, true)).comp ((artinHom m (i, true)).comp
        (artinHom m (i + 1, true))) := by
  have hi : i + 1 < m := by omega
  have hi' : i + 1 + 1 < m := by omega
  refine FreeGroup.ext_hom _ _ fun k ↦ ?_
  obtain ⟨k, hk⟩ := k
  simp only [MonoidHom.comp_apply]
  rcases (by omega : k = i ∨ k = i + 1 ∨ k = i + 1 + 1 ∨
      (k ≠ i ∧ k ≠ i + 1 ∧ k ≠ i + 1 + 1)) with rfl | rfl | rfl | ⟨h1, h2, h3⟩
  · simp (disch := omega) [artinHom_mk_self hi, artinHom_mk_succ hi, artinHom_mk_self hi',
      artinHom_mk_succ hi', artinHom_mk_ne]
    group
  · simp (disch := omega) [artinHom_mk_self hi, artinHom_mk_succ hi, artinHom_mk_self hi',
      artinHom_mk_succ hi', artinHom_mk_ne]
  · simp (disch := omega) [artinHom_mk_self hi, artinHom_mk_succ hi, artinHom_mk_self hi',
      artinHom_mk_succ hi', artinHom_mk_ne]
  · simp (disch := omega) [artinHom_mk_ne]

/-! ### Stabilisation -/

set_option linter.unusedSimpArgs false in
/-- A letter on `m` strands commutes with the inclusion into `m + 1` strands. -/
private theorem artinHom_castSucc {m i : ℕ} (b : Bool) (h : i + 1 < m) :
    (artinHom (m + 1) (i, b)).comp (FreeGroup.map Fin.castSucc) =
      (FreeGroup.map Fin.castSucc).comp (artinHom m (i, b)) := by
  have h' : i + 1 < m + 1 := by omega
  refine FreeGroup.ext_hom _ _ fun k ↦ ?_
  obtain ⟨k, hk⟩ := k
  simp only [MonoidHom.comp_apply, FreeGroup.map.of, Fin.castSucc_mk]
  rcases (by omega : k = i ∨ k = i + 1 ∨ (k ≠ i ∧ k ≠ i + 1)) with rfl | rfl | ⟨h1, h2⟩
  · cases b <;> simp (disch := omega) [artinHom_mk_self h, artinHom_mk_self h']
  · cases b <;> simp (disch := omega) [artinHom_mk_succ h, artinHom_mk_succ h']
  · simp (disch := omega) [artinHom_mk_ne]

/-- A word on `m` strands commutes with the inclusion into `m + 1` strands. -/
private theorem artinAct_castSucc {m : ℕ} {w : BraidWord} (hw : IsOnStrands m w) :
    (artinAct (m + 1) w).comp (FreeGroup.map Fin.castSucc) =
      (FreeGroup.map Fin.castSucc).comp (artinAct m w) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    have hg : g.1 + 1 < m := hw g List.mem_cons_self
    have ih' := ih fun g' hg' ↦ hw g' (List.mem_cons_of_mem _ hg')
    rw [artinAct_cons, artinAct_cons, MonoidHom.comp_assoc, ih', ← MonoidHom.comp_assoc,
      show g = (g.1, g.2) from rfl, artinHom_castSucc g.2 hg, MonoidHom.comp_assoc]

/-- A word on `m` strands fixes the new strand. -/
private theorem artinAct_last {m : ℕ} {w : BraidWord} (hw : IsOnStrands m w) :
    artinAct (m + 1) w (FreeGroup.of (Fin.last m)) = FreeGroup.of (Fin.last m) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    have hg : g.1 + 1 < m := hw g List.mem_cons_self
    rw [artinAct_cons, MonoidHom.comp_apply, ih fun g' hg' ↦ hw g' (List.mem_cons_of_mem _ hg'),
      show g = (g.1, g.2) from rfl]
    exact artinHom_mk_ne g.2 m (by omega) (by omega) (by omega)

/-- The lift of the images of the generators under a homomorphism is the homomorphism. -/
private theorem lift_of_comp_markov {α G : Type*} [Group G] (φ : FreeGroup α →* G) :
    FreeGroup.lift (fun k ↦ φ (FreeGroup.of k)) = φ :=
  FreeGroup.ext_hom _ _ fun k ↦ by simp

/-- The collapse `Fin (n + 2) → Fin (n + 1)` of the two last strands. -/
private def stabCollapse (n : ℕ) (j : Fin (n + 1 + 1)) : Fin (n + 1) :=
  ⟨min (j : ℕ) n, by omega⟩

/-- The relations at the stabilised strands, for a negative stabilisation. -/
private theorem stab_eqs_false {G : Type*} [Group G] {X Y Z : G} (e1 : Y = X)
    (e2 : Y⁻¹ * Z * Y = Y) : X = Y ∧ Z = X := by
  subst e1
  refine ⟨rfl, ?_⟩
  calc Z = Y * (Y⁻¹ * Z * Y) * Y⁻¹ := by group
    _ = Y := by rw [e2]; group

/-- The relations at the stabilised strands, for a positive stabilisation. -/
private theorem stab_eqs_true {G : Type*} [Group G] {X Y Z : G} (e1 : Z * Y * Z⁻¹ = X)
    (e2 : Z = Y) : X = Y ∧ Z = X := by
  subst e2
  rw [mul_inv_cancel_right] at e1
  exact ⟨e1.symm, e1⟩

set_option linter.unusedSimpArgs false in
/-- Markov stabilisation does not change the group. -/
private theorem nonempty_mulEquiv_stabilize {n : ℕ} (w : BraidWord) (b : Bool)
    (hw : IsOnStrands (n + 1) w) :
    Nonempty (PresentedGroup (endRels (artinAct (n + 1) w)) ≃*
      PresentedGroup (endRels (artinAct (n + 1 + 1) (w ++ [(n, b)])))) := by
  have hn : n + 1 < n + 1 + 1 := by omega
  have hφ : artinAct (n + 1 + 1) (w ++ [(n, b)]) =
      (artinAct (n + 1 + 1) w).comp (artinHom (n + 1 + 1) (n, b)) := by
    rw [artinAct_append, artinAct_cons]
    rfl
  rw [hφ]
  set A := artinAct (n + 1) w
  set A' := artinAct (n + 1 + 1) w
  set hb := artinHom (n + 1 + 1) (n, b)
  set ι : FreeGroup (Fin (n + 1)) →* FreeGroup (Fin (n + 1 + 1)) := FreeGroup.map Fin.castSucc
  set ρ : FreeGroup (Fin (n + 1 + 1)) →* FreeGroup (Fin (n + 1)) := FreeGroup.map (stabCollapse n)
  set mk := PresentedGroup.mk (endRels A)
  set mk' := PresentedGroup.mk (endRels (A'.comp hb))
  have hfix' := mk_endRels_map (A'.comp hb)
  have hAι : A'.comp ι = ι.comp A := artinAct_castSucc hw
  have hAl : A' (FreeGroup.of ⟨n + 1, hn⟩) = FreeGroup.of ⟨n + 1, hn⟩ := artinAct_last hw
  have hE : mk' (FreeGroup.of ⟨n, by omega⟩) = mk' (FreeGroup.of ⟨n + 1, hn⟩) ∧
      mk' (A' (FreeGroup.of ⟨n, by omega⟩)) = mk' (FreeGroup.of ⟨n, by omega⟩) := by
    have e1 := hfix' (FreeGroup.of ⟨n, by omega⟩)
    have e2 := hfix' (FreeGroup.of ⟨n + 1, hn⟩)
    simp only [MonoidHom.comp_apply, hb] at e1 e2
    cases b
    · rw [artinHom_mk_self hn] at e1
      rw [artinHom_mk_succ hn] at e2
      simp only [Bool.false_eq_true, ite_false, map_mul, map_inv, hAl] at e1 e2
      exact stab_eqs_false e1 e2
    · rw [artinHom_mk_self hn] at e1
      rw [artinHom_mk_succ hn] at e2
      simp only [ite_true, map_mul, map_inv, hAl] at e1 e2
      exact stab_eqs_true e1 e2
  obtain ⟨hE1, hE2⟩ := hE
  have hρι : ρ.comp ι = MonoidHom.id _ := by
    refine FreeGroup.ext_hom _ _ fun k ↦ ?_
    obtain ⟨k, hk⟩ := k
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, ι, ρ, FreeGroup.map.of, Fin.castSucc_mk,
      stabCollapse]
    congr 2
    omega
  have hρh : ρ.comp hb = ρ := by
    refine FreeGroup.ext_hom _ _ fun j ↦ ?_
    obtain ⟨j, hj⟩ := j
    simp only [MonoidHom.comp_apply, hb]
    rcases (by omega : j = n ∨ j = n + 1 ∨ (j ≠ n ∧ j ≠ n + 1)) with rfl | rfl | ⟨h1, h2⟩
    · rw [artinHom_mk_self hn]
      cases b <;> simp [ρ, FreeGroup.map.of, stabCollapse]
    · rw [artinHom_mk_succ hn]
      cases b <;> simp [ρ, FreeGroup.map.of, stabCollapse]
    · rw [artinHom_mk_ne b j hj h1 h2]
  have hρA : (mk.comp ρ).comp A' = mk.comp ρ := by
    refine FreeGroup.ext_hom _ _ fun j ↦ ?_
    obtain ⟨j, hj⟩ := j
    rcases (by omega : j < n + 1 ∨ j = n + 1) with hj' | rfl
    · have e : (FreeGroup.of ⟨j, hj⟩ : FreeGroup (Fin (n + 1 + 1))) =
          ι (FreeGroup.of ⟨j, hj'⟩) := by simp [ι, FreeGroup.map.of]
      simp only [MonoidHom.comp_apply]
      rw [e, ← MonoidHom.comp_apply A' ι, hAι, MonoidHom.comp_apply, ← MonoidHom.comp_apply ρ ι,
        ← MonoidHom.comp_apply ρ ι, hρι, MonoidHom.id_apply, MonoidHom.id_apply]
      exact mk_endRels_map A _
    · simp only [MonoidHom.comp_apply, hAl]
  let Φ : PresentedGroup (endRels A) →* PresentedGroup (endRels (A'.comp hb)) :=
    PresentedGroup.toGroup (f := fun k ↦ mk' (ι (FreeGroup.of k))) (by
      rintro _ ⟨k, rfl⟩
      obtain ⟨k, hk⟩ := k
      have hl : FreeGroup.lift (fun k ↦ mk' (ι (FreeGroup.of k))) = mk'.comp ι :=
        lift_of_comp_markov (mk'.comp ι)
      rw [hl, MonoidHom.comp_apply, map_mul, map_inv, map_mul,
        map_inv, ← MonoidHom.comp_apply ι A, ← hAι, MonoidHom.comp_apply, inv_mul_eq_one]
      have e : ι (FreeGroup.of ⟨k, hk⟩) = FreeGroup.of ⟨k, by omega⟩ := by
        simp [ι, FreeGroup.map.of]
      rw [e]
      rcases (by omega : k < n ∨ k = n) with hk' | rfl
      · have e2 : hb (FreeGroup.of ⟨k, by omega⟩) = FreeGroup.of ⟨k, by omega⟩ :=
          artinHom_mk_ne b k _ (by omega) (by omega)
        conv_rhs => rw [← e2]
        exact (hfix' _).symm
      · exact hE2.symm)
  let Ψ : PresentedGroup (endRels (A'.comp hb)) →* PresentedGroup (endRels A) :=
    PresentedGroup.toGroup (f := fun j ↦ mk (ρ (FreeGroup.of j))) (by
      rintro _ ⟨j, rfl⟩
      have hl : FreeGroup.lift (fun j ↦ mk (ρ (FreeGroup.of j))) = mk.comp ρ :=
        lift_of_comp_markov (mk.comp ρ)
      have e := DFunLike.congr_fun hρA (hb (FreeGroup.of j))
      have e' := DFunLike.congr_fun hρh (FreeGroup.of j)
      simp only [MonoidHom.comp_apply] at e e'
      rw [hl, MonoidHom.comp_apply, map_mul, map_inv, map_mul, map_inv, MonoidHom.comp_apply,
        e, e', inv_mul_cancel])
  have hΦ : ∀ k, Φ (PresentedGroup.of k) = mk' (ι (FreeGroup.of k)) := fun k ↦
    PresentedGroup.toGroup.of _
  have hΨ : ∀ j, Ψ (PresentedGroup.of j) = mk (ρ (FreeGroup.of j)) := fun j ↦
    PresentedGroup.toGroup.of _
  refine ⟨MonoidHom.toMulEquiv Φ Ψ (PresentedGroup.ext fun k ↦ ?_)
    (PresentedGroup.ext fun j ↦ ?_)⟩
  · rw [MonoidHom.comp_apply, hΦ, MonoidHom.id_apply]
    change Ψ (PresentedGroup.mk _ (ι (FreeGroup.of k))) = _
    obtain ⟨k, hk⟩ := k
    have e : ι (FreeGroup.of ⟨k, hk⟩) = FreeGroup.of ⟨k, by omega⟩ := by
      simp [ι, FreeGroup.map.of]
    rw [e]
    change Ψ (PresentedGroup.of _) = _
    rw [hΨ]
    simp only [ρ, FreeGroup.map.of, stabCollapse]
    congr 2
    simp only [Fin.ext_iff]
    omega
  · rw [MonoidHom.comp_apply, hΨ, MonoidHom.id_apply]
    obtain ⟨j, hj⟩ := j
    change Φ (PresentedGroup.of _) = _
    rw [hΦ]
    simp only [ρ, ι, FreeGroup.map.of, stabCollapse, Fin.castSucc_mk]
    rcases (by omega : j < n + 1 ∨ j = n + 1) with hj' | rfl
    · congr 2
      simp only [Fin.ext_iff]
      omega
    · refine (congrArg (fun t ↦ mk' (FreeGroup.of t)) (Fin.ext ?_)).trans hE1
      simp

/-! ### One Markov step -/

private theorem nonempty_mulEquiv_of_markovStep {c c' : ClosedBraid} (h : MarkovStep c c') :
    Nonempty (PresentedGroup (endRels (artinAct c.1 c.2)) ≃*
      PresentedGroup (endRels (artinAct c'.1 c'.2))) := by
  cases h with
  | @cancel m u v i b h =>
    have e : artinAct m (u ++ (i, b) :: (i, !b) :: v) = artinAct m (u ++ v) := by
      rw [artinAct_append, artinAct_append, artinAct_cons, artinAct_cons]
      congr 1
      rw [← MonoidHom.comp_assoc, artinHom_comp_not h, MonoidHom.id_comp]
    dsimp only
    rw [e]
    exact ⟨MulEquiv.refl _⟩
  | @farComm m u v i j b c hij h =>
    have e : artinAct m (u ++ (i, b) :: (j, c) :: v) =
        artinAct m (u ++ (j, c) :: (i, b) :: v) := by
      rw [artinAct_append, artinAct_append, artinAct_cons, artinAct_cons, artinAct_cons,
        artinAct_cons]
      congr 1
      rw [← MonoidHom.comp_assoc, artinHom_comm b c hij h, MonoidHom.comp_assoc]
    dsimp only
    rw [e]
    exact ⟨MulEquiv.refl _⟩
  | @braidRel m u v i h =>
    have e : artinAct m (u ++ (i, true) :: (i + 1, true) :: (i, true) :: v) =
        artinAct m (u ++ (i + 1, true) :: (i, true) :: (i + 1, true) :: v) := by
      simp only [artinAct_append, artinAct_cons]
      have e2 := congrArg (fun φ ↦ (artinAct m u).comp (φ.comp (artinAct m v)))
        (artinHom_braid h)
      simpa only [MonoidHom.comp_assoc] using e2
    dsimp only
    rw [e]
    exact ⟨MulEquiv.refl _⟩
  | @rotate m w g =>
    dsimp only
    obtain ⟨i, b⟩ := g
    have e1 : artinAct m ((i, b) :: w) = (artinHom m (i, b)).comp (artinAct m w) := rfl
    have e2 : artinAct m (w ++ [(i, b)]) = (artinAct m w).comp (artinHom m (i, b)) := by
      rw [artinAct_append, artinAct_cons]
      rfl
    rw [e1, e2]
    by_cases hi : i + 1 < m
    · refine nonempty_mulEquiv_endRels_of_conj (θ' := artinHom m (i, !b)) ?_
        (artinHom_comp_not hi b) rfl
      have := artinHom_comp_not hi (!b)
      rwa [Bool.not_not] at this
    · exact nonempty_mulEquiv_endRels_of_conj (θ := artinHom m (i, b)) (θ' := MonoidHom.id _)
        (by rw [artinHom_of_not_lt hi]; rfl) (by rw [artinHom_of_not_lt hi]; rfl) rfl
  | @stabilize m w b hm hw =>
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    exact nonempty_mulEquiv_stabilize w b hw

/-- Markov equivalent braid knots have isomorphic knot groups. -/
theorem knotGroup_equiv_of_markovEquiv {K K' : BraidKnot} (hM : MarkovEquiv K K') :
    Nonempty (KnotGroup K ≃* KnotGroup K') := by
  have key : ∀ c c' : ClosedBraid, Relation.EqvGen MarkovStep c c' →
      Nonempty (PresentedGroup (endRels (artinAct c.1 c.2)) ≃*
        PresentedGroup (endRels (artinAct c'.1 c'.2))) := by
    intro c c' hc
    induction hc with
    | rel _ _ h => exact nonempty_mulEquiv_of_markovStep h
    | refl => exact ⟨MulEquiv.refl _⟩
    | symm _ _ _ ih => exact ⟨ih.some.symm⟩
    | trans _ _ _ _ _ ih1 ih2 => exact ⟨ih1.some.trans ih2.some⟩
  have h := key _ _ hM
  unfold KnotGroup
  rw [artinRels_eq_endRels, artinRels_eq_endRels]
  exact h

/-- The companion groups of different admissible pairs are not isomorphic. -/
theorem not_knotGroup_torusPairKnot_equiv {r s r' s' : ℕ} (h : IsTorusPair r s)
    (h' : IsTorusPair r' s') (hne : (r, s) ≠ (r', s')) :
    ¬ Nonempty (KnotGroup (torusPairKnot r s h) ≃* KnotGroup (torusPairKnot r' s' h')) := by
  rintro ⟨e⟩
  obtain ⟨e₁⟩ := knotGroup_torusPairKnot_equiv h
  obtain ⟨e₂⟩ := knotGroup_torusPairKnot_equiv h'
  obtain ⟨q₁⟩ := torusKnotGroup_quot_center h
  obtain ⟨q₂⟩ := torusKnotGroup_quot_center h'
  let f : TorusKnotGroup r s ≃* TorusKnotGroup r' s' := e₁.symm.trans (e.trans e₂)
  let g := QuotientGroup.congr (Subgroup.center (TorusKnotGroup r s))
    (Subgroup.center (TorusKnotGroup r' s')) f (Subgroup.map_center_eq f)
  obtain ⟨hr, hs⟩ := eq_of_mulEquiv_cycCoprod h h' (q₁.symm.trans (g.trans q₂))
  exact hne (by rw [hr, hs])

/-- T-DIST (b), conditional on the JSJ input: different admissible pairs give closed braids that
are not Markov equivalent. -/
theorem pairWhiteheadKnot_not_markovEquiv_of_jsj (hJ : WhiteheadJSJProp) {r s r' s' : ℕ}
    (h : IsTorusPair r s) (h' : IsTorusPair r' s') (hne : (r, s) ≠ (r', s')) :
    ¬ MarkovEquiv (pairWhiteheadKnot r s h) (pairWhiteheadKnot r' s' h') := fun hM ↦
  not_knotGroup_torusPairKnot_equiv h h' hne (hJ r s r' s' h h' (knotGroup_equiv_of_markovEquiv hM))

/-- T-DIST (b) at the level of exteriors, conditional on the JSJ input: different admissible pairs
give doubles with non-isomorphic knot groups. -/
theorem pairWhiteheadKnot_knotGroup_not_equiv_of_jsj (hJ : WhiteheadJSJProp) {r s r' s' : ℕ}
    (h : IsTorusPair r s) (h' : IsTorusPair r' s') (hne : (r, s) ≠ (r', s')) :
    ¬ Nonempty (KnotGroup (pairWhiteheadKnot r s h) ≃* KnotGroup (pairWhiteheadKnot r' s' h')) :=
  fun he ↦ not_knotGroup_torusPairKnot_equiv h h' hne (hJ r s r' s' h h' he)

end AJConjecture
