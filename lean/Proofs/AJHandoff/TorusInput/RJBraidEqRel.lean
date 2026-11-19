import Mathlib
import AJHandoff.TorusInput.RJBraidEqBasic
import AJConjecture.SkeinThickYangBaxter
import AJConjecture.SkeinThickGenInv

/-!
# Braid relations for every profile (node RA5.ii.4)

The braid relation, far commutation, a letter commuting with a word on far strands, and the
derived relation `σ_(i+1) σ_i σ_(i+1)^j = σ_i^j σ_(i+1) σ_i`, all in the sense of `RJBraidEq`.

Route. Braid relation: the profile cables of both sides are the two sides of thick Reidemeister
III, `braidMatrix_thickCross_yangBaxter`, for the thicknesses `κ i`, `κ (i+1)`, `κ (i+2)` at the
offset `profileOffset κ i` (unfold `thickCable`, `profileSwap`, `profileOffset`); both sides
reverse the three columns. Far commutation: the two thick crossings act on disjoint windows
(`braidMatrix_commute_of_far`). The letter past a word: induction on the word with far
commutation. Derived relation: induction on `j`, using the braid relation
`σ_(i+1) σ_i σ_(i+1) = σ_i σ_(i+1) σ_i` once per step and `rj_braidEq_append`. Estimate
120–180 lines.
-/

noncomputable section

namespace AJConjecture

/-- Evaluates a profile at a column after explicit adjacent swaps. -/
local macro "rj_swap_tac" : tactic =>
  `(tactic| (simp only [profileSwap, Equiv.swap_apply_def]; split_ifs <;>
    first | omega | rfl | (congr 1; omega)))

/-- The profile cable of a one-letter word. -/
private theorem rj_thickCable_singleton_braidEqRel (κ : ℕ → ℕ) (g : ℕ × Bool) :
    thickCable κ [g] = thickCross (κ g.1) (κ (g.1 + 1)) (profileOffset κ g.1) g.2 := by
  rw [thickCable, thickCable, List.append_nil]

/-- The profile cable of a word, letter by letter. -/
private theorem rj_thickCable_cons_braidEqRel (κ : ℕ → ℕ) (g : ℕ × Bool) (w : BraidWord) :
    thickCable κ (g :: w) =
      thickCross (κ g.1) (κ (g.1 + 1)) (profileOffset κ g.1) g.2 ++
        thickCable (profileSwap κ g.1) w := rfl

/-- The braid relation for every profile. -/
theorem rj_braidEq_yb (n i : ℕ) (s : Bool) (h : i + 2 < n) :
    RJBraidEq n [(i, s), (i + 1, s), (i, s)] [(i + 1, s), (i, s), (i + 1, s)] := by
  refine ⟨fun g hg ↦ ?_, fun g hg ↦ ?_, fun κ N hN ↦ ⟨?_, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp only <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp only <;> omega
  · have h3 : profileOffset κ i + κ i + κ (i + 1) + κ (i + 2) ≤ N := by
      have := rj_profileOffset_mono κ (show i + 3 ≤ n by omega)
      rw [rj_profileOffset_succ, rj_profileOffset_succ, rj_profileOffset_succ] at this
      omega
    have e1 : ∀ x, x ≤ i → profileOffset (profileSwap (profileSwap κ i) (i + 1)) x =
        profileOffset κ x := fun x hx ↦ by
      rw [rj_profileOffset_profileSwap_of_le _ _ _ (by omega),
        rj_profileOffset_profileSwap_of_le _ _ _ hx]
    have e2 : ∀ x, x ≤ i → profileOffset (profileSwap κ (i + 1)) x =
        profileOffset κ x := fun x hx ↦ rj_profileOffset_profileSwap_of_le _ _ _ (by omega)
    have o1 : profileOffset (profileSwap κ i) (i + 1) = profileOffset κ i + κ (i + 1) := by
      rw [rj_profileOffset_succ, rj_profileOffset_profileSwap_of_le _ _ _ le_rfl, profileSwap,
        Equiv.swap_apply_left]
    have o2 : profileOffset (profileSwap (profileSwap κ (i + 1)) i) (i + 1) =
        profileOffset κ i + κ (i + 2) := by
      rw [rj_profileOffset_succ, rj_profileOffset_profileSwap_of_le _ _ _ le_rfl, e2 i le_rfl]
      rj_swap_tac
    have o3 : profileOffset κ (i + 1) = profileOffset κ i + κ i := rj_profileOffset_succ κ i
    have v1 : profileSwap κ i (i + 1) = κ i := by rj_swap_tac
    have v2 : profileSwap κ i (i + 1 + 1) = κ (i + 2) := by
      rj_swap_tac
    have v3 : profileSwap (profileSwap κ i) (i + 1) i = κ (i + 1) := by
      rj_swap_tac
    have v4 : profileSwap (profileSwap κ i) (i + 1) (i + 1) = κ (i + 2) := by
      rj_swap_tac
    have v5 : profileSwap κ (i + 1) i = κ i := by rj_swap_tac
    have v6 : profileSwap κ (i + 1) (i + 1) = κ (i + 2) := by
      rj_swap_tac
    have v7 : profileSwap (profileSwap κ (i + 1)) i (i + 1) = κ i := by
      rj_swap_tac
    have v8 : profileSwap (profileSwap κ (i + 1)) i (i + 1 + 1) = κ (i + 1) := by
      rj_swap_tac
    rw [rj_thickCable_cons_braidEqRel, rj_thickCable_cons_braidEqRel,
      rj_thickCable_singleton_braidEqRel, rj_thickCable_cons_braidEqRel,
      rj_thickCable_cons_braidEqRel, rj_thickCable_singleton_braidEqRel]
    simp only [braidMatrix_append]
    rw [e1 i le_rfl, o1, o2, e2 i le_rfl, o3, v1, v2, v3, v4, v5, v6, v7, v8,
      show i + 1 + 1 = i + 2 by omega]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact braidMatrix_thickCross_yangBaxter N (κ i) (κ (i + 1)) (κ (i + 2)) _ s h3
  · funext x
    simp only [profileEnd, profileSwap]
    congr 1
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega

/-- Far commutation for every profile. -/
theorem rj_braidEq_far (n i j : ℕ) (s s' : Bool) (hij : i + 1 < j) (hj : j + 1 < n) :
    RJBraidEq n [(i, s), (j, s')] [(j, s'), (i, s)] := by
  refine ⟨fun g hg ↦ ?_, fun g hg ↦ ?_, fun κ N hN ↦ ⟨?_, ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only <;> omega
  · rw [rj_thickCable_cons_braidEqRel, rj_thickCable_singleton_braidEqRel,
      rj_thickCable_cons_braidEqRel, rj_thickCable_singleton_braidEqRel]
    simp only [braidMatrix_append]
    rw [rj_profileOffset_profileSwap_of_lt κ i j hij,
      rj_profileOffset_profileSwap_of_le κ j i (by omega)]
    simp only [profileSwap]
    rw [Equiv.swap_apply_of_ne_of_ne (show j ≠ i by omega) (by omega),
      Equiv.swap_apply_of_ne_of_ne (show j + 1 ≠ i by omega) (by omega),
      Equiv.swap_apply_of_ne_of_ne (show i ≠ j by omega) (by omega),
      Equiv.swap_apply_of_ne_of_ne (show i + 1 ≠ j by omega) (by omega)]
    refine braidMatrix_commute_of_far N _ _ fun g hg g' hg' ↦ ?_
    have h1 := rj_mem_thickCross hg
    have h2 := rj_mem_thickCross hg'
    have h3 := rj_profileOffset_mono κ (show i + 2 ≤ j by omega)
    rw [rj_profileOffset_succ, rj_profileOffset_succ] at h3
    omega
  · funext x
    simp only [profileEnd, profileSwap]
    congr 1
    simp only [Equiv.swap_apply_def]
    split_ifs <;> omega

/-- A letter commutes with a word whose letters are all far from it. -/
theorem rj_braidEq_letter_word (n i : ℕ) (s : Bool) (w : BraidWord) (hi : i + 1 < n)
    (hw : IsOnStrands n w) (hfar : ∀ g ∈ w, g.1 + 1 < i ∨ i + 1 < g.1) :
    RJBraidEq n ((i, s) :: w) (w ++ [(i, s)]) := by
  induction w with
  | nil =>
    refine rj_braidEq_refl n _ fun g hg ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    exact hi
  | cons g w ih =>
    have hw' : IsOnStrands n w := fun g' hg' ↦ hw g' (List.mem_cons_of_mem _ hg')
    have hg : g.1 + 1 < n := hw g List.mem_cons_self
    have ih' := ih hw' fun g' hg' ↦ hfar g' (List.mem_cons_of_mem _ hg')
    have hswap : RJBraidEq n [(i, s), g] [g, (i, s)] := by
      rcases hfar g List.mem_cons_self with h | h
      · exact rj_braidEq_symm (rj_braidEq_far n g.1 i g.2 s h hi)
      · exact rj_braidEq_far n i g.1 s g.2 h hg
    have h1 := rj_braidEq_append hswap (rj_braidEq_refl n w hw')
    have h2 := rj_braidEq_append (rj_braidEq_refl n [g] fun g' hg' ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
      subst hg'
      exact hg) ih'
    exact rj_braidEq_trans h1 h2

/-- `σ_(i+1) σ_i σ_(i+1)^j = σ_i^j σ_(i+1) σ_i` for every profile. -/
theorem rj_braidEq_slide_pow (n i j : ℕ) (h : i + 2 < n) :
    RJBraidEq n ([(i + 1, true), (i, true)] ++ List.replicate j (i + 1, true))
      (List.replicate j (i, true) ++ [(i + 1, true), (i, true)]) := by
  have hx : IsOnStrands n [(i, true)] := fun g hg ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    simp only
    omega
  have hy : IsOnStrands n [(i + 1, true)] := fun g hg ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    simp only
    omega
  induction j with
  | zero =>
    refine rj_braidEq_refl n _ fun g hg ↦ ?_
    simp only [List.replicate_zero, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp only <;> omega
  | succ j ih =>
    have h1 := rj_braidEq_append ih (rj_braidEq_refl n _ hy)
    have h2 := rj_braidEq_append (rj_braidEq_refl n (List.replicate j (i, true)) fun g hg ↦ by
      rw [List.eq_of_mem_replicate hg]
      simp only
      omega) (rj_braidEq_symm (rj_braidEq_yb n i true h))
    rw [List.replicate_succ', List.replicate_succ', ← List.append_assoc]
    refine rj_braidEq_trans h1 ?_
    simpa only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
      using h2

end AJConjecture
