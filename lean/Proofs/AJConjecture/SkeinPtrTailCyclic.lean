import Mathlib
import AJConjecture.SkeinPtrTailBasic
import AJConjecture.SkeinPartialTrace
import AJConjecture.SkeinPlaceAppend

/-!
# Partial cyclicity and the closure by a thick cup and cap

An operator `C` on the traced factors that commutes with their weight can be moved cyclically
inside the partial trace. The partial trace over the last `r` factors is the closure by a
thick cup and a thick cap on the right: the weights are `cup(a, ā) cap(a, ā) = μ(a)`.
-/

namespace AJConjecture

/-- Proves an equality between two values of states that are defined by cases on the
position. -/
local macro "state_cases_ptrTailCyclic" : tactic =>
  `(tactic| (simp only [append_apply_dite, Fin.val_cast]
             split_ifs <;> first | rfl | (exfalso; omega) |
               (congr 1; exact Fin.ext (by first | (simp only [Fin.val_rev]; omega) | omega))))

/-- A sum over the states of `k + 2r` factors is a double sum. -/
private theorem sum_states_two_mul_ptrTailCyclic {k r : ℕ}
    (f : (Fin (k + 2 * r) → Bool) → RatFunc ℚ) :
    ∑ c, f c = ∑ c : Fin (k + r) → Bool, ∑ e : Fin r → Bool,
      f (fun x ↦ Fin.append c e (Fin.cast (by omega) x)) := by
  have hcast : ∀ {n m : ℕ} (h : n = m) (g : (Fin n → Bool) → RatFunc ℚ),
      ∑ c, g c = ∑ c : Fin m → Bool, g (fun x ↦ c (Fin.cast h x)) := by
    intro n m h g
    subst h
    rfl
  rw [hcast (show k + 2 * r = k + r + r by omega) f, sum_append_states]

/-- The entries of a thick cup on a concatenated state. -/
private theorem cupThick_append_apply_ptrTailCyclic (r : ℕ) (u : Fin 0 → Bool)
    (c e : Fin r → Bool) :
    cupThick r u (fun y : Fin (2 * r) ↦ Fin.append c e (Fin.cast (two_mul r) y)) =
      ∏ x, cupEntry (c x) (e (Fin.rev x)) := by
  rw [cupThick, Matrix.of_apply]
  refine Finset.prod_congr rfl fun x _ ↦ ?_
  congr 1 <;> state_cases_ptrTailCyclic

/-- The entries of a thick cap on a concatenated state. -/
private theorem capThick_append_apply_ptrTailCyclic (r : ℕ) (u : Fin 0 → Bool)
    (c e : Fin r → Bool) :
    capThick r (fun y : Fin (2 * r) ↦ Fin.append c e (Fin.cast (two_mul r) y)) u =
      ∏ x, capEntry (c x) (e (Fin.rev x)) := by
  rw [capThick, Matrix.of_apply]
  refine Finset.prod_congr rfl fun x _ ↦ ?_
  congr 1 <;> state_cases_ptrTailCyclic

/-- A thick cup followed by a thick cap on the same factors is the weight. -/
private theorem sum_cupEntry_mul_capEntry_ptrTailCyclic (r : ℕ) (c d : Fin r → Bool) :
    ∑ e : Fin r → Bool, (∏ x, cupEntry (c x) (e (Fin.rev x))) *
        ∏ x, capEntry (d x) (e (Fin.rev x)) =
      if c = d then ∏ x, skWeightEntry (c x) else 0 := by
  have h1 : ∀ p q : Bool, ∑ t : Bool, cupEntry p t * capEntry q t =
      if p = q then skWeightEntry p else 0 := by
    intro p q
    cases p <;> cases q <;> simp [cupEntry, capEntry, skWeightEntry]
  calc ∑ e : Fin r → Bool, (∏ x, cupEntry (c x) (e (Fin.rev x))) *
        ∏ x, capEntry (d x) (e (Fin.rev x))
      = ∑ e : Fin r → Bool, ∏ x, cupEntry (c x) (e x) * capEntry (d x) (e x) := by
        refine Fintype.sum_equiv (Equiv.arrowCongr Fin.revPerm (Equiv.refl Bool)) _ _ fun e ↦ ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun x _ ↦ ?_
        simp [Equiv.arrowCongr]
    _ = ∏ x, ∑ t : Bool, cupEntry (c x) t * capEntry (d x) t :=
        (Fintype.prod_sum fun x t ↦ cupEntry (c x) t * capEntry (d x) t).symm
    _ = ∏ x, if c x = d x then skWeightEntry (c x) else 0 := by simp only [h1]
    _ = if c = d then ∏ x, skWeightEntry (c x) else 0 := by
        rw [Fintype.prod_ite_zero]
        by_cases h : c = d
        · rw [ite_eq_left h, ite_eq_left fun i ↦ congrFun h i]
        · rw [ite_eq_right h, ite_eq_right fun h' ↦ h (funext h')]

/-- The entries of a thick cup placed on the right of `k` strands. -/
private theorem skPlace_cupThick_apply_ptrTailCyclic (k r : ℕ) (a c₁ : Fin k → Bool)
    (c₂ c₃ : Fin r → Bool) :
    skPlace k (k + 2 * r) k (cupThick r) a
        (fun x ↦ Fin.append (Fin.append c₁ c₂) c₃ (Fin.cast (by omega) x)) =
      if a = c₁ then ∏ x, cupEntry (c₂ x) (c₃ (Fin.rev x)) else 0 := by
  rw [skPlace_apply_of_eq (n := k) (n' := k + 2 * r) k 0 (cupThick r) rfl rfl a
    (fun x ↦ Fin.append (Fin.append c₁ c₂) c₃ (Fin.cast (by omega) x)) a c₁ Fin.elim0
    (fun y : Fin (2 * r) ↦ Fin.append c₂ c₃ (Fin.cast (two_mul r) y)) Fin.elim0 Fin.elim0
    (fun x ↦ by state_cases_ptrTailCyclic) (fun x ↦ by state_cases_ptrTailCyclic),
    cupThick_append_apply_ptrTailCyclic]
  simp

/-- The entries of a thick cap placed on the right of `k` strands. -/
private theorem skPlace_capThick_apply_ptrTailCyclic (k r : ℕ) (b d₁ : Fin k → Bool)
    (d₂ d₃ : Fin r → Bool) :
    skPlace (k + 2 * r) k k (capThick r)
        (fun x ↦ Fin.append (Fin.append d₁ d₂) d₃ (Fin.cast (by omega) x)) b =
      if d₁ = b then ∏ x, capEntry (d₂ x) (d₃ (Fin.rev x)) else 0 := by
  rw [skPlace_apply_of_eq (n := k + 2 * r) (n' := k) k 0 (capThick r) rfl rfl
    (fun x ↦ Fin.append (Fin.append d₁ d₂) d₃ (Fin.cast (by omega) x)) b d₁ b
    (fun y : Fin (2 * r) ↦ Fin.append d₂ d₃ (Fin.cast (two_mul r) y)) Fin.elim0 Fin.elim0
    Fin.elim0 (fun x ↦ by state_cases_ptrTailCyclic) (fun x ↦ by state_cases_ptrTailCyclic),
    capThick_append_apply_ptrTailCyclic]
  simp

/-- The entries of an operator on the first `k + r` of `k + 2r` factors. -/
private theorem skPlace_head_apply_ptrTailCyclic (k r : ℕ) (A : SkMat (k + r) (k + r))
    (c d : Fin (k + r) → Bool) (e f : Fin r → Bool) :
    skPlace (k + 2 * r) (k + 2 * r) 0 A (fun x ↦ Fin.append c e (Fin.cast (by omega) x))
        (fun x ↦ Fin.append d f (Fin.cast (by omega) x)) =
      if e = f then A c d else 0 := by
  rw [skPlace_apply_of_eq 0 r A (by omega) (by omega)
    (fun x ↦ Fin.append c e (Fin.cast (by omega) x))
    (fun x ↦ Fin.append d f (Fin.cast (by omega) x)) Fin.elim0 Fin.elim0 c d e f
    (fun x ↦ by state_cases_ptrTailCyclic) (fun x ↦ by state_cases_ptrTailCyclic)]
  simp

/-- The partial trace over the last `r` factors is the closure by a thick cup and a thick cap. -/
theorem ptrTail_eq_cupThick_capThick (k r : ℕ) (A : SkMat (k + r) (k + r)) :
    ptrTail k (k + r) A =
      skPlace k (k + 2 * r) k (cupThick r) * skPlace (k + 2 * r) (k + 2 * r) 0 A *
        skPlace (k + 2 * r) k k (capThick r) := by
  ext a b
  rw [ptrTail_append_apply, Matrix.mul_apply]
  simp only [Matrix.mul_apply, sum_states_two_mul_ptrTailCyclic]
  simp only [skPlace_head_apply_ptrTailCyclic, sum_append_states,
    skPlace_cupThick_apply_ptrTailCyclic, skPlace_capThick_apply_ptrTailCyclic, ite_mul,
    zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  calc ∑ s, (∏ x, skWeightEntry (s x)) * A (Fin.append a s) (Fin.append b s)
      = ∑ d : Fin r → Bool, ∑ c : Fin r → Bool, A (Fin.append a c) (Fin.append b d) *
          ∑ e : Fin r → Bool, (∏ x, cupEntry (c x) (e (Fin.rev x))) *
            ∏ x, capEntry (d x) (e (Fin.rev x)) := by
        simp only [sum_cupEntry_mul_capEntry_ptrTailCyclic, mul_ite, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        exact Finset.sum_congr rfl fun s _ ↦ mul_comm _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
        ring

end AJConjecture
