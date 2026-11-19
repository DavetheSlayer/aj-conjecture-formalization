import Mathlib
import AJFamily.Skein.TorusPhaseTwoGadget
import AJFamily.Skein.TorusPhaseTwoPass

/-!
# Stage T of phase II: the twists travel to the clasp

`phaseTwo_stageT`: the negative full twists on the input band, a bead on the band, pass the doubled
crossings of the first pass (`morseReach_beadD_left`, `morseReach_beadD_pow'`), go around the
doubled closing cap (macro `TWCAP`, by induction) and move down the closing arc next to the clasp.
-/

namespace AJConjecture

/-- The letters of a run of doubled crossings are crossings on the strands `0 … 3`. -/
private theorem mem_phaseTwoBlk_D_bundle {m : ℕ} {b : MorseLetter}
    (hb : b ∈ phaseTwoBlk phaseTwoD m) : (∃ s, b.1 = MorseKind.cross s) ∧ b.2 ≤ 2 := by
  simp only [phaseTwoBlk, List.mem_flatten, List.mem_replicate] at hb
  obtain ⟨l, ⟨-, rfl⟩, hb⟩ := hb
  simp only [phaseTwoD, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact ⟨⟨true, rfl⟩, by decide⟩

/-- A run of doubled crossings does not change the number of strands. -/
private theorem morseOut_phaseTwoBlk_D_bundle (n m : ℕ) :
    morseOut n (phaseTwoBlk phaseTwoD m) = n :=
  morseOut_of_cross n _ fun _ hb ↦ (mem_phaseTwoBlk_D_bundle hb).1

/-- A run of equal crossings does not change the number of strands. -/
private theorem morseOut_replicate_cross_bundle (n i m : ℕ) (s : Bool) :
    morseOut n (List.replicate m (MorseKind.cross s, i)) = n :=
  morseOut_of_cross n _ fun _ hb ↦ by rw [List.eq_of_mem_replicate hb]; exact ⟨s, rfl⟩

/-- A run of equal crossings fits when one crossing does. -/
private theorem morseFits_replicate_cross_bundle (n i m : ℕ) (s : Bool) (h : i + 2 ≤ n) :
    morseFits n (List.replicate m (MorseKind.cross s, i)) = true :=
  morseFits_of_cross n _ (fun _ hb ↦ by rw [List.eq_of_mem_replicate hb]; exact ⟨s, rfl⟩)
    (fun _ hb ↦ by rw [List.eq_of_mem_replicate hb]; exact h)

/-- The negative twists `(−2)^(2m)` pass the doubled closing cap `n3 n2` (macro `TWCAP`, framed
with `d = 2`, applied `m` times) and become `(−4)^(2m)`. -/
private theorem morseReach_twists_pass_cap_bundle (m : ℕ) :
    ∀ u v : MorseWord, morseOut 1 u = 7 →
      MorseReach 1 (u ++ List.replicate (2 * m) (MorseKind.cross false, 2) ++
          [(MorseKind.cap, 3), (MorseKind.cap, 2)] ++ v)
        (u ++ List.replicate (2 * m) (MorseKind.cross false, 4) ++
          [(MorseKind.cap, 3), (MorseKind.cap, 2)] ++ v) := by
  induction m with
  | zero => intro u v _; exact morseReach_refl 1 _
  | succ m ih =>
    intro u v hu
    have hm : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    have hu' : morseOut 1 (u ++ List.replicate (2 * m) (MorseKind.cross false, 2)) = 2 + 4 + 1 := by
      rw [morseOut_append, hu, morseOut_replicate_cross_bundle]
    have h1 := morseReach_frame 4 1 2 1 (u ++ List.replicate (2 * m) (MorseKind.cross false, 2)) v
      _ _ morseReach_phaseTwoMacroTWCAP phaseTwoMacroTWCAP_fits hu'
    have hl : morseShiftWord 2 phaseTwoMacroTWCAP_lhs = [(MorseKind.cross false, 2),
        (MorseKind.cross false, 2), (MorseKind.cap, 3), (MorseKind.cap, 2)] := rfl
    have hr : morseShiftWord 2 phaseTwoMacroTWCAP_rhs = [(MorseKind.cross false, 4),
        (MorseKind.cross false, 4), (MorseKind.cap, 3), (MorseKind.cap, 2)] := rfl
    rw [hl, hr] at h1
    have h2 := morseReach_symm (morseReach_comm 1 u
      (List.replicate (2 * m) (MorseKind.cross false, 2))
      [(MorseKind.cross false, 4), (MorseKind.cross false, 4)]
      ([(MorseKind.cap, 3), (MorseKind.cap, 2)] ++ v)
      (fun _ hb ↦ by rw [List.eq_of_mem_replicate hb]; exact ⟨false, rfl⟩)
      (fun _ hb a ha ↦ by
        rw [List.eq_of_mem_replicate hb]
        simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ha
        rw [ha])
      (by
        rw [hu, morseFits_append,
          show morseOut 7 [(MorseKind.cross false, 4), (MorseKind.cross false, 4)] = 7 from rfl,
          morseFits_replicate_cross_bundle 7 2 _ false (by decide)]
        rfl))
    have h3 := ih (u ++ [(MorseKind.cross false, 4), (MorseKind.cross false, 4)]) v
      (by rw [morseOut_append, hu]; rfl)
    rw [hm, List.replicate_succ', List.replicate_succ', List.replicate_succ,
      List.replicate_succ]
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)

set_option linter.unusedVariables false in
/-- Stage T: the twists join the clasp. -/
theorem phaseTwo_stageT (k : ℕ) (hk : 1 ≤ k) : MorseReach 1 (phaseTwoWC k) (phaseTwoWT k) := by
  set T : MorseWord := List.replicate (4 * k) (MorseKind.cross false, 0) with hT
  set Dk : MorseWord := phaseTwoBlk phaseTwoD (2 * k) with hDk
  set C3 : MorseWord := [(MorseKind.cup, 1), (MorseKind.cup, 2), (MorseKind.cup, 3)] with hC3
  have hTf : morseFits 2 T = true := morseFits_replicate_cross_bundle 2 0 _ false le_rfl
  have hTo : morseOut 2 T = 2 := morseOut_replicate_cross_bundle 2 0 _ false
  have hsT : morseShiftWord 2 T = List.replicate (4 * k) (MorseKind.cross false, 2) := by
    simp only [hT, morseShiftWord, List.map_replicate, shiftLetter]
  -- the cups move to the front
  have h1 := morseReach_symm (morseReach_comm 1 [(MorseKind.cup, 1)] T
    [(MorseKind.cup, 2), (MorseKind.cup, 3)]
    (phaseTwoD ++ phaseTwoClaspS ++ Dk ++
      [(.cross false, 2), (.cross false, 2), (.cap, 3), (.cap, 2), (.cap, 1)])
    (fun _ hb ↦ by rw [List.eq_of_mem_replicate hb]; exact ⟨false, rfl⟩)
    (fun _ hb a ha ↦ by
      rw [List.eq_of_mem_replicate hb]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> decide)
    (by
      rw [morseFits_append]
      exact morseFits_replicate_cross_bundle 7 0 _ false (by decide)))
  -- the bundle passes the first doubled crossing
  have h2 := morseReach_beadD_left 1 C3 T (phaseTwoClaspS ++ Dk ++
      [(.cross false, 2), (.cross false, 2), (.cap, 3), (.cap, 2), (.cap, 1)]) hTf hTo
    (by decide)
  -- the clasp moves in front of the bundle
  have h3 := morseReach_symm (morseReach_comm 1 (C3 ++ phaseTwoD) (morseShiftWord 2 T)
    phaseTwoClaspS
    (Dk ++ [(.cross false, 2), (.cross false, 2), (.cap, 3), (.cap, 2), (.cap, 1)])
    (fun _ hb ↦ by rw [hsT] at hb; rw [List.eq_of_mem_replicate hb]; exact ⟨false, rfl⟩)
    (fun _ hb a ha ↦ by
      rw [hsT] at hb
      rw [List.eq_of_mem_replicate hb]
      simp only [phaseTwoClaspS, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      rw [show morseOut 1 (C3 ++ phaseTwoD) = 7 by decide, morseFits_append,
        show morseFits 7 phaseTwoClaspS = true by decide,
        show morseOut 7 phaseTwoClaspS = 7 by decide, hsT,
        morseFits_replicate_cross_bundle 7 2 _ false (by decide)]
      rfl))
  -- the bundle passes the remaining doubled crossings
  have h4 := morseReach_beadD_pow' 1 (2 * k) (C3 ++ phaseTwoD ++ phaseTwoClaspS) T
    ([(.cross false, 2), (.cross false, 2), (.cap, 3), (.cap, 2), (.cap, 1)]) hTf hTo
    (by decide)
  simp only [Nat.mul_mod_right, ↓reduceIte] at h4
  -- the twists pass the doubled closing cap
  have hu5 : morseOut 1 (C3 ++ phaseTwoD ++ phaseTwoClaspS ++ Dk) = 7 := by
    rw [morseOut_append, show morseOut 1 (C3 ++ phaseTwoD ++ phaseTwoClaspS) = 7 by decide,
      hDk, morseOut_phaseTwoBlk_D_bundle]
  have h5 := morseReach_twists_pass_cap_bundle (2 * k + 1)
    (C3 ++ phaseTwoD ++ phaseTwoClaspS ++ Dk) [(MorseKind.cap, 1)] hu5
  -- the twists move down the closing arc
  have h6 := morseReach_symm (morseReach_comm 1 (C3 ++ phaseTwoD ++ phaseTwoClaspS) Dk
    (List.replicate (2 * (2 * k + 1)) (MorseKind.cross false, 4))
    [(MorseKind.cap, 3), (MorseKind.cap, 2), (MorseKind.cap, 1)]
    (fun _ hb ↦ (mem_phaseTwoBlk_D_bundle hb).1)
    (fun _ hb a ha ↦ by
      rw [List.eq_of_mem_replicate ha]
      have := (mem_phaseTwoBlk_D_bundle hb).2
      simp only
      omega)
    (by
      rw [show morseOut 1 (C3 ++ phaseTwoD ++ phaseTwoClaspS) = 7 by decide, morseFits_append,
        morseFits_replicate_cross_bundle 7 4 _ false (by decide), morseOut_replicate_cross_bundle]
      exact morseFits_of_cross 7 _ (fun _ hb ↦ (mem_phaseTwoBlk_D_bundle hb).1)
        (fun _ hb ↦ by have := (mem_phaseTwoBlk_D_bundle hb).2; omega)))
  have hrep : List.replicate (4 * k) (MorseKind.cross false, 2) ++
      [(MorseKind.cross false, 2), (MorseKind.cross false, 2)] =
      List.replicate (2 * (2 * k + 1)) (MorseKind.cross false, 2) := by
    rw [show 2 * (2 * k + 1) = 4 * k + 2 by ring, List.replicate_add]
    rfl
  rw [hsT] at h2 h3 h4
  have e4 : C3 ++ phaseTwoD ++ phaseTwoClaspS ++ Dk ++
      List.replicate (4 * k) (MorseKind.cross false, 2) ++
      [(.cross false, 2), (.cross false, 2), (.cap, 3), (.cap, 2), (.cap, 1)] =
      C3 ++ phaseTwoD ++ phaseTwoClaspS ++ Dk ++
        List.replicate (2 * (2 * k + 1)) (MorseKind.cross false, 2) ++
        [(MorseKind.cap, 3), (MorseKind.cap, 2)] ++ [(MorseKind.cap, 1)] := by
    rw [← hrep]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [e4] at h4
  have hWC : phaseTwoWC k = [(MorseKind.cup, 1)] ++ T ++
      [(MorseKind.cup, 2), (MorseKind.cup, 3)] ++ (phaseTwoD ++ phaseTwoClaspS ++ Dk ++
        [(.cross false, 2), (.cross false, 2), (.cap, 3), (.cap, 2), (.cap, 1)]) := by
    simp only [phaseTwoWC, hT, hDk, List.append_assoc]
  have hWT : phaseTwoWT k = C3 ++ phaseTwoD ++ phaseTwoClaspS ++
      List.replicate (2 * (2 * k + 1)) (MorseKind.cross false, 4) ++ Dk ++
      [(MorseKind.cap, 3), (MorseKind.cap, 2), (MorseKind.cap, 1)] := by
    simp only [phaseTwoWT, hC3, hDk, List.append_assoc]
  rw [hWC, hWT]
  simp only [hC3, List.append_assoc, List.cons_append, List.nil_append]
    at h1 h2 h3 h4 h5 h6 ⊢
  exact morseReach_trans h1 (morseReach_trans h2 (morseReach_trans h3 (morseReach_trans h4
    (morseReach_trans h5 h6))))

end AJConjecture
