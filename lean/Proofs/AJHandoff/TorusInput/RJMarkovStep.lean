import Mathlib
import AJHandoff.TorusInput.RJMarkovConj
import AJHandoff.TorusInput.RJBraidEqRel
import AJHandoff.TorusInput.RJMarkovDestab

/-!
# Unwinding the axis, one strand at a time (node RA5.ii.7, crux)

`⟨β(m+2, p)⟩ = θ_b ⟨β(m+1, p+1)⟩` for the profile `(b, …, b, k)`, where
`β(m, p) = σ_(m-1)^(2p) · FT_m · c_m` (`rjBetaWord`): the closure of the cyclic braid on `m`
bundles of `b` strands together with an axis of `k` strands, the axis twisted `p` more times with
the last bundle. Iterated: `⟨β(m+1, p)⟩ = θ_b^m ⟨β(1, p+m)⟩`.

Route (verified numerically step by step, design notes). Put `y = σ_(m+1)`, `x = σ_m`; by
definition `β(m+2,p) = y^(2p) · y · FT_(m+1) · y · c_(m+1) · x`.
1. `y c_(m+1) ≈ c_(m+1) y` (`rj_braidEq_letter_word`).
2. Conjugate `y^(2p+1)` to the end (`rj_colorTrace_append_comm`).
3. `y x y^(2p+1) ≈ x^(2p+1) y x` (`rj_braidEq_slide_pow`).
4. Conjugate the last `x` to the front; the bottom profile is now `(b,…,b,k,b,b)`.
5. Destabilize the last letter `y` (`rj_colorTrace_destab`, the last two columns have
   thickness `b`).
6. Conjugate `x^(2p+1)` to the front: `x^(2p+2) FT_(m+1) c_(m+1) = β(m+1, p+1)`, profile
   `(b,…,b,k)` on the columns `≤ m + 1` (`rj_colorTrace_congr`).
The profiles at each step are computed with `profileEnd`, `profileSwap`. Estimate 180–260
lines.
-/

noncomputable section

namespace AJConjecture

/-- Evaluates an explicit profile at a column. -/
local macro "rj_prof_tac" : tactic =>
  `(tactic| (simp only [profileSwap, rjAxisProfile, Equiv.swap_apply_def]; split_ifs <;>
    first | omega | rfl))

/-- A concatenation of words on `n` strands is on `n` strands. -/
private theorem rj_isOnStrands_append_markovStep {n : ℕ} {u v : BraidWord}
    (hu : IsOnStrands n u) (hv : IsOnStrands n v) : IsOnStrands n (u ++ v) := fun g hg ↦ by
  rcases List.mem_append.mp hg with hg | hg
  · exact hu g hg
  · exact hv g hg

/-- A word on `n` strands is on more strands. -/
private theorem rj_isOnStrands_mono_markovStep {n n' : ℕ} {w : BraidWord} (h : n ≤ n')
    (hw : IsOnStrands n w) : IsOnStrands n' w := fun g hg ↦ by
  have := hw g hg
  omega

/-- A power of one letter. -/
private theorem rj_isOnStrands_replicate_markovStep (n j i : ℕ) (s : Bool) (h : i + 1 < n) :
    IsOnStrands n (List.replicate j (i, s)) := fun g hg ↦ by
  rw [List.eq_of_mem_replicate hg]
  exact h

/-- The axis word on `m + 1` strands. -/
private theorem rj_isOnStrands_axisWord_markovStep (m : ℕ) :
    IsOnStrands (m + 1) (rjAxisWord m) := by
  induction m with
  | zero => intro g hg; simp [rjAxisWord] at hg
  | succ m ih =>
    intro g hg
    rw [rjAxisWord, List.mem_cons, List.mem_append, List.mem_singleton] at hg
    rcases hg with rfl | hg | rfl
    · simp only; omega
    · have := ih g hg; omega
    · simp only; omega

/-- The cyclic word on `m` strands. -/
private theorem rj_isOnStrands_cycleWord_markovStep (m : ℕ) : IsOnStrands m (rjCycleWord m) :=
  fun g hg ↦ by
    simp only [rjCycleWord, List.mem_map, List.mem_range] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    simp only
    omega

/-- Swapping the same two columns twice restores the profile. -/
private theorem rj_profileSwap_profileSwap_markovStep (κ : ℕ → ℕ) (i : ℕ) :
    profileSwap (profileSwap κ i) i = κ := by
  funext x
  simp only [profileSwap, Equiv.swap_apply_self]

/-- The axis word does not permute the columns. -/
private theorem rj_profileEnd_axisWord_markovStep (m : ℕ) (κ : ℕ → ℕ) :
    profileEnd κ (rjAxisWord m) = κ := by
  induction m generalizing κ with
  | zero => rfl
  | succ m ih =>
    rw [rjAxisWord, profileEnd, rj_profileEnd_append, ih, profileEnd, profileEnd,
      rj_profileSwap_profileSwap_markovStep]

/-- A word on `n` strands keeps a profile that is constant on the columns `< n`. -/
private theorem rj_profileEnd_of_const_markovStep (κ : ℕ → ℕ) (n b : ℕ) (w : BraidWord)
    (hw : IsOnStrands n w) (h : ∀ x < n, κ x = b) : profileEnd κ w = κ := by
  induction w generalizing κ with
  | nil => rfl
  | cons g w ih =>
    have hg : g.1 + 1 < n := hw g List.mem_cons_self
    have hs : profileSwap κ g.1 = κ := by
      funext x
      simp only [profileSwap, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, h (g.1 + 1) hg, h g.1 (by omega)]
      · rw [h2, h (g.1 + 1) hg, h g.1 (by omega)]
      · rfl
    rw [profileEnd, hs]
    exact ih κ (fun g' hg' ↦ hw g' (List.mem_cons_of_mem _ hg')) h

/-- An odd power of a letter swaps its two columns. -/
private theorem rj_profileEnd_replicate_odd_markovStep (κ : ℕ → ℕ) (j : ℕ) (g : ℕ × Bool) :
    profileEnd κ (List.replicate (2 * j + 1) g) = profileSwap κ g.1 := by
  induction j generalizing κ with
  | zero => rfl
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, List.replicate_succ,
      List.replicate_succ, profileEnd, profileEnd, rj_profileSwap_profileSwap_markovStep, ih]

/-- The first move: the axis letter passes the cyclic word. -/
private theorem rj_colorTrace_step_one_markovStep (b k m p : ℕ) :
    rjColorTrace (rjAxisProfile b k (m + 2)) (m + 3) (rjBetaWord (m + 2) p) =
      rjColorTrace (rjAxisProfile b k (m + 2)) (m + 3)
        (List.replicate (2 * p + 1) (m + 1, true) ++
          (rjAxisWord (m + 1) ++ rjCycleWord (m + 1) ++ [(m + 1, true), (m, true)])) := by
  set A := rjAxisWord (m + 1)
  set C := rjCycleWord (m + 1)
  have hA : IsOnStrands (m + 3) A :=
    rj_isOnStrands_mono_markovStep (by omega) (rj_isOnStrands_axisWord_markovStep (m + 1))
  have hC : IsOnStrands (m + 3) C :=
    rj_isOnStrands_mono_markovStep (by omega) (rj_isOnStrands_cycleWord_markovStep (m + 1))
  set U := List.replicate (2 * p + 1) (m + 1, true) ++ A
  have hU : IsOnStrands (m + 3) U :=
    rj_isOnStrands_append_markovStep (rj_isOnStrands_replicate_markovStep _ _ _ _ (by omega)) hA
  have hx : IsOnStrands (m + 3) [(m, true)] :=
    rj_isOnStrands_replicate_markovStep (m + 3) 1 m true (by omega)
  have hlw := rj_braidEq_letter_word (m + 3) (m + 1) true C (by omega) hC fun g hg ↦ by
    have := rj_isOnStrands_cycleWord_markovStep (m + 1) g hg
    omega
  have h := rj_braidEq_append (rj_braidEq_append (rj_braidEq_refl _ U hU) hlw)
    (rj_braidEq_refl _ _ hx)
  have hc2 : rjCycleWord (m + 2) = C ++ [(m, true)] := by
    simp only [C, rjCycleWord, show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega,
      List.range_succ, List.map_append, List.map_singleton]
  have ha2 : rjAxisWord (m + 2) = (m + 1, true) :: (A ++ [(m + 1, true)]) := rfl
  have e1 : rjBetaWord (m + 2) p = U ++ ((m + 1, true) :: C) ++ [(m, true)] := by
    rw [rjBetaWord, ha2, hc2, show m + 2 - 1 = m + 1 by omega]
    simp only [U, List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append]
  have e2 : List.replicate (2 * p + 1) (m + 1, true) ++ (A ++ C ++ [(m + 1, true), (m, true)]) =
      U ++ (C ++ [(m + 1, true)]) ++ [(m, true)] := by
    simp only [U, List.append_assoc, List.cons_append, List.nil_append]
  rw [e1, e2]
  exact rj_colorTrace_of_braidEq _ h

/-- Profile values in the six moves: the profile after `y^(2p+1)`. -/
private theorem rj_prof_one_markovStep (b k m z : ℕ) (hz : z < m + 1) :
    profileSwap (rjAxisProfile b k (m + 2)) (m + 1) z = b := by
  rj_prof_tac

/-- Profile values in the six moves: the profile after the destabilization. -/
private theorem rj_prof_three_markovStep (b k m z : ℕ) (hz : z < m + 1) :
    profileSwap (profileSwap (profileSwap (profileSwap (rjAxisProfile b k (m + 2)) (m + 1)) m)
      (m + 1)) m z = b := by
  rj_prof_tac

/-- Profile values in the six moves: the closure condition of the second move. -/
private theorem rj_prof_close_two_markovStep (b k m z : ℕ) :
    profileSwap (profileSwap (profileSwap (rjAxisProfile b k (m + 2)) (m + 1)) (m + 1)) m z =
      rjAxisProfile b k (m + 2) z := by
  rj_prof_tac

/-- Profile values in the six moves: the closure condition of the fourth move. -/
private theorem rj_prof_close_four_markovStep (b k m z : ℕ) :
    profileSwap (profileSwap (profileSwap (profileSwap (rjAxisProfile b k (m + 2)) (m + 1)) m)
      (m + 1)) m z = profileSwap (rjAxisProfile b k (m + 2)) (m + 1) z := by
  rj_prof_tac

/-- Profile values in the six moves: the two last columns before the destabilization. -/
private theorem rj_prof_destab_markovStep (b k m : ℕ) :
    profileSwap (profileSwap (profileSwap (rjAxisProfile b k (m + 2)) (m + 1)) m) (m + 1)
        (m + 1) = b ∧
      profileSwap (profileSwap (profileSwap (rjAxisProfile b k (m + 2)) (m + 1)) m) (m + 1)
        (m + 2) = b := by
  constructor <;> rj_prof_tac

/-- Profile values in the six moves: the final profile. -/
private theorem rj_prof_final_markovStep (b k m z : ℕ) (hz : z < m + 2) :
    profileSwap (profileSwap (profileSwap (profileSwap (rjAxisProfile b k (m + 2)) (m + 1)) m)
      (m + 1)) m z = rjAxisProfile b k (m + 1) z := by
  rj_prof_tac

/-- One destabilization: the axis winds once more around one bundle fewer. -/
theorem rj_colorTrace_beta_succ (b k m p : ℕ) :
    rjColorTrace (rjAxisProfile b k (m + 2)) (m + 3) (rjBetaWord (m + 2) p) =
      kinkScalar b *
        rjColorTrace (rjAxisProfile b k (m + 1)) (m + 2) (rjBetaWord (m + 1) (p + 1)) := by
  set A := rjAxisWord (m + 1) with hAdef
  set C := rjCycleWord (m + 1) with hCdef
  set κ := rjAxisProfile b k (m + 2) with hκ
  set κ1 := profileSwap κ (m + 1) with hκ1
  set κ2 := profileSwap (profileSwap κ1 m) (m + 1) with hκ2
  set κ3 := profileSwap κ2 m with hκ3
  set X := List.replicate (2 * p + 1) (m, true) with hX
  set Y := List.replicate (2 * p + 1) (m + 1, true) with hY
  have hA : IsOnStrands (m + 2) A := rj_isOnStrands_axisWord_markovStep (m + 1)
  have hC : IsOnStrands (m + 1) C := rj_isOnStrands_cycleWord_markovStep (m + 1)
  have hXs : IsOnStrands (m + 2) X := rj_isOnStrands_replicate_markovStep _ _ _ _ (by omega)
  have hYs : IsOnStrands (m + 3) Y := rj_isOnStrands_replicate_markovStep _ _ _ _ (by omega)
  have hx : IsOnStrands (m + 2) [(m, true)] :=
    rj_isOnStrands_replicate_markovStep (m + 2) 1 m true (by omega)
  have hy : IsOnStrands (m + 3) [(m + 1, true)] :=
    rj_isOnStrands_replicate_markovStep (m + 3) 1 (m + 1) true (by omega)
  have hAC : IsOnStrands (m + 3) (A ++ C) := rj_isOnStrands_append_markovStep
    (rj_isOnStrands_mono_markovStep (by omega) hA) (rj_isOnStrands_mono_markovStep (by omega) hC)
  have hκc : ∀ z < m + 1, κ1 z = b := fun z hz ↦ rj_prof_one_markovStep b k m z hz
  have hκ3c : ∀ z < m + 1, κ3 z = b := fun z hz ↦ rj_prof_three_markovStep b k m z hz
  have hpC : ∀ ρ : ℕ → ℕ, (∀ z < m + 1, ρ z = b) → profileEnd ρ C = ρ := fun ρ hρ ↦
    rj_profileEnd_of_const_markovStep ρ (m + 1) b C hC hρ
  have hpA : ∀ ρ : ℕ → ℕ, profileEnd ρ A = ρ := rj_profileEnd_axisWord_markovStep (m + 1)
  -- move 2: conjugate `y^(2p+1)` to the end
  have s2 : rjColorTrace κ (m + 3) (Y ++ (A ++ C ++ [(m + 1, true), (m, true)])) =
      rjColorTrace κ1 (m + 3) ((A ++ C ++ [(m + 1, true), (m, true)]) ++ Y) := by
    rw [rj_colorTrace_append_comm κ (m + 3) Y _ hYs
      (rj_isOnStrands_append_markovStep hAC (fun g hg ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl <;> simp only <;> omega)) ?_,
      hY, rj_profileEnd_replicate_odd_markovStep]
    intro z hz
    rw [rj_profileEnd_append, hY, rj_profileEnd_replicate_odd_markovStep, rj_profileEnd_append,
      rj_profileEnd_append, hpA, hpC _ hκc]
    exact rj_prof_close_two_markovStep b k m z
  -- move 3: `y x y^(2p+1) = x^(2p+1) y x`
  have s3 : rjColorTrace κ1 (m + 3) ((A ++ C ++ [(m + 1, true), (m, true)]) ++ Y) =
      rjColorTrace κ1 (m + 3) ((A ++ C ++ X ++ [(m + 1, true)]) ++ [(m, true)]) := by
    have h := rj_braidEq_append (rj_braidEq_refl _ _ hAC) (rj_braidEq_slide_pow (m + 3) m
      (2 * p + 1) (by omega))
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h ⊢
    exact rj_colorTrace_of_braidEq _ h
  -- move 4: conjugate the last `x` to the front
  have hp4 : profileEnd κ1 (A ++ C ++ X ++ [(m + 1, true)]) = κ2 := by
    rw [rj_profileEnd_append, rj_profileEnd_append, rj_profileEnd_append, hpA, hpC _ hκc, hX,
      rj_profileEnd_replicate_odd_markovStep]
    rfl
  have s4 : rjColorTrace κ1 (m + 3) ((A ++ C ++ X ++ [(m + 1, true)]) ++ [(m, true)]) =
      rjColorTrace κ2 (m + 3) ([(m, true)] ++ (A ++ C ++ X ++ [(m + 1, true)])) := by
    rw [rj_colorTrace_append_comm κ1 (m + 3) _ [(m, true)]
      (rj_isOnStrands_append_markovStep (rj_isOnStrands_append_markovStep hAC
        (rj_isOnStrands_mono_markovStep (by omega) hXs)) hy)
      (rj_isOnStrands_mono_markovStep (by omega) hx) ?_, hp4]
    intro z hz
    rw [rj_profileEnd_append, hp4]
    exact rj_prof_close_four_markovStep b k m z
  -- move 5: destabilize the last letter
  have hp5 : profileEnd κ2 ([(m, true)] ++ A ++ C) = κ3 := by
    rw [rj_profileEnd_append, rj_profileEnd_append, hpA,
      show profileEnd κ2 [(m, true)] = κ3 from rfl, hpC _ hκ3c]
  have hw5 : IsOnStrands (m + 2) ([(m, true)] ++ A ++ C ++ X) :=
    rj_isOnStrands_append_markovStep (rj_isOnStrands_append_markovStep
      (rj_isOnStrands_append_markovStep hx hA) (rj_isOnStrands_mono_markovStep (by omega) hC)) hXs
  have hend5 : ∀ z, profileEnd κ2 ([(m, true)] ++ A ++ C ++ X) z = κ2 z := fun z ↦ by
    rw [rj_profileEnd_append, hp5, hX, rj_profileEnd_replicate_odd_markovStep]
    show profileSwap κ3 m z = κ2 z
    rw [hκ3, rj_profileSwap_profileSwap_markovStep]
  have s5 : rjColorTrace κ2 (m + 3) ([(m, true)] ++ (A ++ C ++ X ++ [(m + 1, true)])) =
      kinkScalar b * rjColorTrace κ2 (m + 2) ([(m, true)] ++ A ++ C ++ X) := by
    have h := rj_colorTrace_destab κ2 (m + 1) ([(m, true)] ++ A ++ C ++ X) hw5
      ((rj_prof_destab_markovStep b k m).1.trans (rj_prof_destab_markovStep b k m).2.symm)
      fun z _ ↦ hend5 z
    have hb : κ2 (m + 1) = b := (rj_prof_destab_markovStep b k m).1
    rw [hb] at h
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h ⊢
    exact h
  -- move 6: conjugate `x^(2p+1)` to the front
  have s6 : rjColorTrace κ2 (m + 2) ([(m, true)] ++ A ++ C ++ X) =
      rjColorTrace κ3 (m + 2) (X ++ ([(m, true)] ++ A ++ C)) := by
    rw [rj_colorTrace_append_comm κ2 (m + 2) _ X (rj_isOnStrands_append_markovStep
      (rj_isOnStrands_append_markovStep hx hA) (rj_isOnStrands_mono_markovStep (by omega) hC))
      hXs fun z _ ↦ hend5 z, hp5]
  have s7 : rjColorTrace κ3 (m + 2) (X ++ ([(m, true)] ++ A ++ C)) =
      rjColorTrace (rjAxisProfile b k (m + 1)) (m + 2) (rjBetaWord (m + 1) (p + 1)) := by
    have e : X ++ ([(m, true)] ++ A ++ C) = rjBetaWord (m + 1) (p + 1) := by
      rw [rjBetaWord, show m + 1 - 1 = m by omega, show 2 * (p + 1) = 2 * p + 1 + 1 by ring,
        List.replicate_succ', hX]
      simp only [List.append_assoc, hAdef, hCdef]
    rw [e]
    exact rj_colorTrace_congr _ _ (m + 2) _ (by
      rw [← e]
      exact rj_isOnStrands_append_markovStep hXs (rj_isOnStrands_append_markovStep
        (rj_isOnStrands_append_markovStep hx hA) (rj_isOnStrands_mono_markovStep (by omega) hC)))
      fun z hz ↦ rj_prof_final_markovStep b k m z hz
  rw [rj_colorTrace_step_one_markovStep, s2, s3, s4, s5, s6, s7]

/-- All destabilizations: the closure of the cyclic braid with its axis becomes `T(2, 2(m+1+p))`
on one bundle. -/
theorem rj_colorTrace_beta (b k m p : ℕ) :
    rjColorTrace (rjAxisProfile b k (m + 1)) (m + 2) (rjBetaWord (m + 1) p) =
      kinkScalar b ^ m * rjColorTrace (rjAxisProfile b k 1) 2 (rjBetaWord 1 (p + m)) := by
  induction m generalizing p with
  | zero => simp only [pow_zero, one_mul, Nat.add_zero, Nat.zero_add]
  | succ m ih =>
    rw [rj_colorTrace_beta_succ, ih (p + 1), pow_succ, show p + 1 + m = p + (m + 1) by ring]
    ring

end AJConjecture
