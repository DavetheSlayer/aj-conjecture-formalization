import Mathlib
import AJFamily.Skein.MorseFrame
import AJFamily.Skein.TorusPhaseOneMacros
import AJFamily.Skein.TorusPhaseOneShared

/-!
# Phase I: the three top level steps

The level steps `4k + 1`, `4k` and `4k - 1`: `phaseOneSource k` → `phaseOneTop1 k` →
`phaseOneTop2 k` → `phaseOneStair k (4k-1)`, where `phaseOneSource_eq` identifies the source with
the long closure of the family word. Each step chains fixed macros of `TorusPhaseOneMacros`, steps
of `TorusPhaseOneShared` and generic moves.
-/

namespace AJConjecture

/-! ### Private helpers: the frame lemma -/

/-- One move, transported into a frame. -/
private theorem morseApply_frame_top (n n₀ d e : ℕ) (u v w w' : MorseWord) (mv : MorseMove)
    (h : morseApply n w mv = some w') (hfit : morseFits n w = true)
    (hu : morseOut n₀ u = d + n + e) :
    MorseReach n₀ (u ++ morseShiftWord d w ++ v) (u ++ morseShiftWord d w' ++ v) ∧
      morseFits n w' = true := by
  obtain ⟨p, r, bk⟩ := mv
  obtain ⟨a, rest, -, rfl, rfl, hok, hs, hd⟩ := morseApply_shape n w w' p r bk h
  obtain ⟨hL, hR, hok'⟩ := shiftRule_sides d r hok
  have hSD : morseOut (morseOut n a) (if bk then morseRuleRhs r else morseRuleLhs r) =
      morseOut (morseOut n a) (if bk then morseRuleLhs r else morseRuleRhs r) := by
    cases bk
    · exact morseOut_rule_sides r _ hok hs hd
    · exact (morseOut_rule_sides r _ hok hd hs).symm
  generalize hS : (if bk then morseRuleRhs r else morseRuleLhs r) = S at hs hfit hSD
  generalize hD : (if bk then morseRuleLhs r else morseRuleRhs r) = D at hd hSD
  have hS' : (if bk then morseRuleRhs (shiftRule d r) else morseRuleLhs (shiftRule d r)) =
      morseShiftWord d S := by
    rw [← hS]
    cases bk <;> simp [hL, hR]
  have hD' : (if bk then morseRuleLhs (shiftRule d r) else morseRuleRhs (shiftRule d r)) =
      morseShiftWord d D := by
    rw [← hD]
    cases bk <;> simp [hL, hR]
  rw [morseFits_append, morseFits_append, Bool.and_eq_true, Bool.and_eq_true,
    morseOut_append] at hfit
  obtain ⟨⟨ha, -⟩, hrest⟩ := hfit
  have hA := morseOut_fits_shift n d e a ha
  have hP : morseOut n₀ (u ++ morseShiftWord d a) = d + morseOut n a + e := by
    rw [morseOut_append, hu, hA.1]
  refine ⟨⟨[((u ++ morseShiftWord d a).length, shiftRule d r, bk)], ?_⟩, ?_⟩
  · have := morseApply_junction n₀ (u ++ morseShiftWord d a) (morseShiftWord d rest ++ v)
      (shiftRule d r) bk hok' (by rw [hS', hP]; exact (morseOut_fits_shift _ d e S hs).2)
      (by rw [hD', hP]; exact (morseOut_fits_shift _ d e D hd).2)
    rw [hS', hD'] at this
    simp only [morseApplyAll, morseShiftWord_append, List.append_assoc] at this ⊢
    rw [this]
    rfl
  · rw [morseFits_append, morseFits_append, ha, hd, morseOut_append, ← hSD, hrest]
    rfl

/-- A list of moves, transported into a frame. -/
private theorem morseApplyAll_frame_top (n n₀ d e : ℕ) (u v : MorseWord)
    (hu : morseOut n₀ u = d + n + e) (mvs : List MorseMove) :
    ∀ w w' : MorseWord, morseApplyAll n w mvs = some w' → morseFits n w = true →
      MorseReach n₀ (u ++ morseShiftWord d w ++ v) (u ++ morseShiftWord d w' ++ v) := by
  induction mvs with
  | nil =>
    intro w w' h _
    simp only [morseApplyAll, Option.some.injEq] at h
    subst h
    exact morseReach_refl _ _
  | cons mv mvs ih =>
    intro w w' h hfit
    simp only [morseApplyAll] at h
    cases h₁ : morseApply n w mv with
    | none => simp [h₁] at h
    | some w₁ =>
      rw [h₁, Option.bind_some] at h
      obtain ⟨h2, hf⟩ := morseApply_frame_top n n₀ d e u v w w₁ mv h₁ hfit hu
      exact morseReach_trans h2 (ih w₁ w' h hf)

/-! ### Word helpers -/

/-- A band of width two. -/
private theorem morseBand_two_top (i : ℕ) :
    morseBand i (i + 2) =
      [(MorseKind.cross true, i + 1), (MorseKind.cross true, i),
        (MorseKind.cross false, i + 1)] := by
  rw [morseBand_succ i (i + 1) (by omega)]
  simp [morseBand, morseOfBraid, surfaceBand]

/-- The letters of the small climbs. -/
private theorem mem_morseClimbRun_top {n : ℕ} {b : MorseLetter} (hb : b ∈ morseClimbRun n) :
    b.1 = MorseKind.cross true ∧ b.2 + 1 ≤ n := by
  simp only [morseClimbRun, List.mem_map, List.mem_range] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  exact ⟨rfl, hi⟩

/-- The letters of the small climbs and the big climb. -/
private theorem mem_climbs_top {k : ℕ} (hk : 1 ≤ k) {b : MorseLetter}
    (hb : b ∈ morseClimbRun (2 * k - 1) ++ morseBand (2 * k - 1) (4 * k)) :
    (∃ s, b.1 = MorseKind.cross s) ∧ b.2 + 1 ≤ 4 * k := by
  rcases List.mem_append.mp hb with h | h
  · have := mem_morseClimbRun_top h
    exact ⟨⟨true, this.1⟩, by omega⟩
  · exact ⟨(mem_morseBand (by omega) h).1, (mem_morseBand (by omega) h).2.2⟩

/-- The letters of the staircase, the last crossing and the final climb of the top step. -/
private theorem mem_topTail_top {k : ℕ} (hk : 1 ≤ k) {b : MorseLetter}
    (hb : b ∈ morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++
      morseBand (2 * k) (4 * k + 1)) :
    (∃ s, b.1 = MorseKind.cross s) ∧ b.2 ≤ 4 * k := by
  rcases List.mem_append.mp hb with h | h
  · rcases List.mem_append.mp h with h | h
    · exact ⟨(mem_morseStairRun h).1, by have := (mem_morseStairRun h).2.2; omega⟩
    · exact ⟨(mem_morseBand (by omega) h).1,
        by have := (mem_morseBand (by omega) h).2.2; omega⟩
  · exact ⟨(mem_morseBand (by omega) h).1, by have := (mem_morseBand (by omega) h).2.2; omega⟩

/-- A short word to the right of a word of crossings commutes with it (positions bounded by
`m`). -/
private theorem morseReach_comm_top (u x y v : MorseWord) (m : ℕ)
    (hx : ∀ b ∈ x, (∃ s, b.1 = MorseKind.cross s) ∧ b.2 + 2 ≤ m)
    (hy : ∀ a ∈ y, m ≤ a.2) (hfit : morseFits (morseOut 1 u) y = true)
    (hN : m ≤ morseOut 1 (u ++ y)) :
    MorseReach 1 (u ++ y ++ x ++ v) (u ++ x ++ y ++ v) :=
  morseReach_comm 1 u x y v (fun b hb ↦ (hx b hb).1)
    (fun b hb a ha ↦ (hx b hb).2.trans (hy a ha))
    (by
      rw [morseFits_append, hfit, Bool.true_and, ← morseOut_append]
      exact morseFits_of_cross _ _ (fun b hb ↦ (hx b hb).1) fun b hb ↦ (hx b hb).2.trans hN)

/-- Closes arity goals on explicit letters. -/
local macro "top_fits" : tactic =>
  `(tactic| ((try simp only [morseOut_append, morseOut, morseLetterOut, morseFits_cons,
    morseFits_nil, morseKindIn, morseKindOut, and_true]) <;> omega))

/-- Closes the identities of explicit shifted words. -/
local macro "top_shift" : tactic =>
  `(tactic| ((try simp only [morseShiftWord, shiftLetter, List.map_cons, List.map_nil,
    List.cons.injEq, Prod.mk.injEq, true_and, and_true, List.cons_append, List.nil_append]) <;>
    omega))

/-- Closes the position goals of a short word. -/
local macro "top_mem" : tactic =>
  `(tactic| (simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] <;> omega))

/-- The staircase of the source word. -/
private theorem morseOfBraid_stair_top (k : ℕ) (hk : 1 ≤ k) :
    morseOfBraid ((List.range (2 * k - 1)).flatMap fun s ↦
        surfaceBand (4 * k - 2 - s) (4 * k - s)) =
      morseStairRun (2 * k) (4 * k - 2) := by
  rw [morseStairRun, show 4 * k - 2 + 1 - 2 * k = 2 * k - 1 by omega, List.range_eq_range',
    List.reverse_range', List.flatMap_map, morseOfBraid, List.map_flatMap, ← List.range_eq_range']
  refine List.flatMap_congr fun s hs ↦ ?_
  rw [List.mem_range] at hs
  rw [morseBand, morseOfBraid]
  congr 2 <;> omega

/-- The source word, cut into its pieces. -/
theorem phaseOneSource_eq (k : ℕ) (hk : 1 ≤ k) :
    morseLongClosure (4 * k + 3) (whiteheadTorusWord k) = phaseOneSource k := by
  have hcup : ((List.range (4 * k + 3 - 1)).map fun j ↦ (MorseKind.cup, j + 1)) =
      morseCupRun 1 (4 * k + 2) := by
    rw [morseCupRun, show 4 * k + 2 + 1 - 1 = 4 * k + 3 - 1 by omega]
    exact List.map_congr_left fun j _ ↦ by rw [Nat.add_comm]
  have hcap : ((List.range (4 * k + 3 - 1)).reverse.map fun j ↦ (MorseKind.cap, j + 1)) =
      morseCapRun (4 * k + 2) := rfl
  rw [morseLongClosure, hcup, hcap, phaseOneSource, whiteheadTorusWord,
    ← morseOfBraid_stair_top k hk]
  simp only [morseOfBraid, morseBand, morseClimbRun, List.map_append, List.map_map,
    List.append_assoc]
  rfl

/-- Level `4k + 1`: the flip. -/
theorem phaseOne_stepS0_flip (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (phaseOneSource k) (phaseOneS0Mid k) := by
  have hCo : morseOut 1 (morseCupRun 1 (4 * k + 1)) = 8 * k + 3 := by
    rw [morseOut_morseCupRun _ _ _ le_rfl]
    omega
  have hAo : ∀ n, morseOut n (morseClimbRun (2 * k - 1) ++ morseBand (2 * k - 1) (4 * k)) = n :=
    fun n ↦ morseOut_of_cross n _ fun b hb ↦ (mem_climbs_top hk hb).1
  have hTo : ∀ n, morseOut n (morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++
      morseBand (2 * k) (4 * k + 1)) = n :=
    fun n ↦ morseOut_of_cross n _ fun b hb ↦ (mem_topTail_top hk hb).1
  have h1 := morseReach_frame 1 1 (4 * k + 2) (4 * k) (morseCupRun 1 (4 * k + 1))
    (morseClimbRun (2 * k - 1) ++ morseBand (2 * k - 1) (4 * k) ++
      [(.cross true, 4 * k), (.cross true, 4 * k - 1), (.cross false, 4 * k),
        (.cross false, 4 * k + 1)] ++
      (morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++
        morseBand (2 * k) (4 * k + 1)) ++ [(.cross false, 4 * k + 1)] ++ morseCapRun (4 * k + 2))
    _ _ morseReach_phaseOneMacroHC phaseOneMacroHC_fits (by rw [hCo]; omega)
  have e1l : morseShiftWord (4 * k + 2) phaseOneMacroHC_lhs = [(.cup, 4 * k + 2)] := by
    simp only [phaseOneMacroHC_lhs]; top_shift
  have e1r : morseShiftWord (4 * k + 2) phaseOneMacroHC_rhs =
      [(.cup, 4 * k + 3), (.cross true, 4 * k + 2), (.cross true, 4 * k + 3)] := by
    simp only [phaseOneMacroHC_rhs]; top_shift
  rw [e1l, e1r] at h1
  have h2 := morseReach_comm_top (morseCupRun 1 (4 * k + 1) ++ [(.cup, 4 * k + 3)])
    (morseClimbRun (2 * k - 1) ++ morseBand (2 * k - 1) (4 * k))
    [(.cross true, 4 * k + 2), (.cross true, 4 * k + 3)]
    ([(.cross true, 4 * k), (.cross true, 4 * k - 1), (.cross false, 4 * k),
        (.cross false, 4 * k + 1)] ++
      (morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++
        morseBand (2 * k) (4 * k + 1)) ++ [(.cross false, 4 * k + 1)] ++ morseCapRun (4 * k + 2))
    (4 * k + 2)
    (fun b hb ↦ ⟨(mem_climbs_top hk hb).1, by have := (mem_climbs_top hk hb).2; omega⟩)
    (by top_mem) (by rw [morseOut_append, hCo]; top_fits)
    (by rw [morseOut_append, morseOut_append, hCo]; top_fits)
  have h3 := morseReach_frame 6 1 (4 * k - 1) (4 * k)
    (morseCupRun 1 (4 * k + 1) ++ [(.cup, 4 * k + 3)] ++
      (morseClimbRun (2 * k - 1) ++ morseBand (2 * k - 1) (4 * k)))
    ((morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++
        morseBand (2 * k) (4 * k + 1)) ++ [(.cross false, 4 * k + 1)] ++ morseCapRun (4 * k + 2))
    _ _ morseReach_phaseOneMacroS0a phaseOneMacroS0a_fits
    (by rw [morseOut_append, hAo, morseOut_append, hCo]; top_fits)
  have e3l : morseShiftWord (4 * k - 1) phaseOneMacroS0a_lhs =
      [(.cross true, 4 * k + 2), (.cross true, 4 * k + 3), (.cross true, 4 * k),
        (.cross true, 4 * k - 1), (.cross false, 4 * k), (.cross false, 4 * k + 1)] := by
    simp only [phaseOneMacroS0a_lhs]; top_shift
  have e3r : morseShiftWord (4 * k - 1) phaseOneMacroS0a_rhs =
      [(.cross true, 4 * k), (.cross true, 4 * k - 1), (.cross false, 4 * k),
        (.cross true, 4 * k + 2), (.cross false, 4 * k + 1), (.cross false, 4 * k + 2),
        (.cross true, 4 * k + 2), (.cross true, 4 * k + 3)] := by
    simp only [phaseOneMacroS0a_rhs]; top_shift
  rw [e3l, e3r] at h3
  have h4 := morseReach_comm_top (morseCupRun 1 (4 * k + 1) ++ [(.cup, 4 * k + 3)] ++
      (morseClimbRun (2 * k - 1) ++ morseBand (2 * k - 1) (4 * k)) ++
      [(.cross true, 4 * k), (.cross true, 4 * k - 1), (.cross false, 4 * k),
        (.cross true, 4 * k + 2), (.cross false, 4 * k + 1), (.cross false, 4 * k + 2)])
    (morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++
        morseBand (2 * k) (4 * k + 1))
    [(.cross true, 4 * k + 2), (.cross true, 4 * k + 3)]
    ([(.cross false, 4 * k + 1)] ++ morseCapRun (4 * k + 2))
    (4 * k + 2)
    (fun b hb ↦ ⟨(mem_topTail_top hk hb).1, by have := (mem_topTail_top hk hb).2; omega⟩)
    (by top_mem) (by rw [morseOut_append, morseOut_append, hAo, morseOut_append, hCo]; top_fits)
    (by rw [morseOut_append, morseOut_append, morseOut_append, hAo, morseOut_append, hCo]; top_fits)
  have h5 := morseReach_frame 4 1 (4 * k + 1) (4 * k)
    (morseCupRun 1 (4 * k + 1) ++ [(.cup, 4 * k + 3)] ++
      (morseClimbRun (2 * k - 1) ++ morseBand (2 * k - 1) (4 * k)) ++
      [(.cross true, 4 * k), (.cross true, 4 * k - 1), (.cross false, 4 * k),
        (.cross true, 4 * k + 2), (.cross false, 4 * k + 1), (.cross false, 4 * k + 2)] ++
      (morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++
        morseBand (2 * k) (4 * k + 1)) ++ [(.cross true, 4 * k + 2)])
    (morseCapRun (4 * k)) _ _ morseReach_phaseOneMacroS0b phaseOneMacroS0b_fits
    (by
      rw [morseOut_append, morseOut_append, hTo, morseOut_append, morseOut_append, hAo,
        morseOut_append, hCo]
      top_fits)
  have e5l : morseShiftWord (4 * k + 1) phaseOneMacroS0b_lhs =
      [(.cross true, 4 * k + 3), (.cross false, 4 * k + 1), (.cap, 4 * k + 2),
        (.cap, 4 * k + 1)] := by
    simp only [phaseOneMacroS0b_lhs]; top_shift
  have e5r : morseShiftWord (4 * k + 1) phaseOneMacroS0b_rhs =
      [(.cap, 4 * k + 2), (.cap, 4 * k + 1)] := by
    simp only [phaseOneMacroS0b_rhs]; top_shift
  rw [e5l, e5r] at h5
  have hcap : morseCapRun (4 * k + 2) =
      (.cap, 4 * k + 2) :: (.cap, 4 * k + 1) :: morseCapRun (4 * k) := by
    rw [morseCapRun_succ, morseCapRun_succ]
  have hb2 : morseBand (4 * k - 1) (4 * k + 1) =
      [(.cross true, 4 * k), (.cross true, 4 * k - 1), (.cross false, 4 * k)] := by
    have := morseBand_two_top (4 * k - 1)
    rwa [show 4 * k - 1 + 2 = 4 * k + 1 by omega, show 4 * k - 1 + 1 = 4 * k by omega] at this
  rw [phaseOneSource, phaseOneS0Mid, morseCupRun_succ 1 (4 * k + 1) (by omega), hb2]
  rw [hcap] at h1 h2 h3 h4 ⊢
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 h4 h5 ⊢
  exact morseReach_trans h1 <| morseReach_trans h2 <| morseReach_trans h3 <|
    morseReach_trans h4 h5

/-- Level `4k + 1`: the retraction (two cups travel right, then the head shuffle). -/
theorem phaseOne_stepS0_retract (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (phaseOneS0Mid k) (phaseOneTop1 k) := by
  have hCo : morseOut 1 (morseCupRun 1 (4 * k)) = 8 * k + 1 := by
    rw [morseOut_morseCupRun _ _ _ le_rfl]
    omega
  have ha := morseReach_comm_top (morseCupRun 1 (4 * k) ++ [(.cup, 4 * k + 1)])
    (morseClimbRun (2 * k - 1) ++ morseBand (2 * k - 1) (4 * k) ++
      [(.cross true, 4 * k), (.cross true, 4 * k - 1), (.cross false, 4 * k)])
    [(.cup, 4 * k + 3)]
    ([(.cross true, 4 * k + 2), (.cross false, 4 * k + 1), (.cross false, 4 * k + 2)] ++
      (morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++
        morseBand (2 * k) (4 * k + 1)) ++ [(.cross true, 4 * k + 2)] ++ morseCapRun (4 * k + 2))
    (4 * k + 2)
    (fun b hb ↦ by
      rcases List.mem_append.mp hb with h | h
      · exact ⟨(mem_climbs_top hk h).1, by have := (mem_climbs_top hk h).2; omega⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl <;> exact ⟨⟨_, rfl⟩, by dsimp only; omega⟩)
    (by top_mem) (by rw [morseOut_append, hCo]; top_fits)
    (by rw [morseOut_append, morseOut_append, hCo]; top_fits)
  have hb := morseReach_comm_top (morseCupRun 1 (4 * k))
    (morseClimbRun (2 * k - 1) ++ morseBand (2 * k - 1) (4 * k)) [(.cup, 4 * k + 1)]
    ([(.cross true, 4 * k), (.cross true, 4 * k - 1), (.cross false, 4 * k)] ++
      [(.cup, 4 * k + 3)] ++
      [(.cross true, 4 * k + 2), (.cross false, 4 * k + 1), (.cross false, 4 * k + 2)] ++
      (morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++
        morseBand (2 * k) (4 * k + 1)) ++ [(.cross true, 4 * k + 2)] ++ morseCapRun (4 * k + 2))
    (4 * k + 1)
    (fun b hb ↦ ⟨(mem_climbs_top hk hb).1, by have := (mem_climbs_top hk hb).2; omega⟩)
    (by top_mem) (by rw [hCo]; top_fits) (by rw [morseOut_append, hCo]; top_fits)
  have hc := morseReach_headShuffle (4 * k) (2 * k - 1) (by omega)
    (morseBand (2 * k - 1) (4 * k) ++ [(.cup, 4 * k + 1)] ++
      [(.cross true, 4 * k), (.cross true, 4 * k - 1), (.cross false, 4 * k)] ++
      [(.cup, 4 * k + 3)] ++
      [(.cross true, 4 * k + 2), (.cross false, 4 * k + 1), (.cross false, 4 * k + 2)] ++
      (morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++
        morseBand (2 * k) (4 * k + 1)) ++ [(.cross true, 4 * k + 2)] ++ morseCapRun (4 * k + 2))
  rw [show 2 * k - 1 + 1 = 2 * k by omega] at hc
  rw [phaseOneS0Mid, phaseOneTop1, morseCupRun_succ 1 (4 * k) (by omega)]
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ha hb hc ⊢
  exact morseReach_trans ha <| morseReach_trans hb hc

/-- Level `4k`. -/
theorem phaseOne_stepS1 (k : ℕ) (hk : 1 ≤ k) :
    MorseReach 1 (phaseOneTop1 k) (phaseOneTop2 k) := by
  have hU : morseOut 1 (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) (4 * k) ++
      morseBand (2 * k - 1) (4 * k)) = 8 * k + 1 := by
    rw [morseOut_append, morseOut_head_cups k (4 * k) hk (by omega),
      morseOut_of_cross _ _ fun b hb ↦ (mem_morseBand (by omega) hb).1]
    omega
  have h1 := morseReach_frame 3 1 (4 * k - 1) (4 * k - 1)
    (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) (4 * k) ++ morseBand (2 * k - 1) (4 * k))
    (morseStairRun (2 * k) (4 * k - 2) ++ morseBand 0 (2 * k + 1) ++
      morseBand (2 * k) (4 * k + 1) ++ [(.cross true, 4 * k + 2)] ++ morseCapRun (4 * k + 2))
    _ _ morseReach_phaseOneMacroS1a phaseOneMacroS1a_fits (by rw [hU]; omega)
  have e1l : morseShiftWord (4 * k - 1) phaseOneMacroS1a_lhs =
      [(.cup, 4 * k + 1), (.cross true, 4 * k), (.cross true, 4 * k - 1), (.cross false, 4 * k),
        (.cup, 4 * k + 3), (.cross true, 4 * k + 2), (.cross false, 4 * k + 1),
        (.cross false, 4 * k + 2)] := by
    simp only [phaseOneMacroS1a_lhs]; top_shift
  have e1r : morseShiftWord (4 * k - 1) phaseOneMacroS1a_rhs =
      [(.cup, 4 * k + 2), (.cross true, 4 * k + 1), (.cross true, 4 * k),
        (.cross true, 4 * k - 1), (.cross false, 4 * k), (.cross false, 4 * k + 1)] ++
      [(.cup, 4 * k + 4), (.cross true, 4 * k + 3), (.cross false, 4 * k + 2),
        (.cross false, 4 * k + 3)] ++
      [(.cross true, 4 * k + 1), (.cross true, 4 * k + 2), (.cross true, 4 * k + 3),
        (.cross true, 4 * k + 4)] := by
    simp only [phaseOneMacroS1a_rhs]; top_shift
  rw [e1l, e1r] at h1
  have hu : morseOut 1 (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) (4 * k) ++
      morseBand (2 * k - 1) (4 * k) ++
      [(.cup, 4 * k + 2), (.cross true, 4 * k + 1), (.cross true, 4 * k),
        (.cross true, 4 * k - 1), (.cross false, 4 * k), (.cross false, 4 * k + 1)] ++
      [(.cup, 4 * k + 4), (.cross true, 4 * k + 3), (.cross false, 4 * k + 2),
        (.cross false, 4 * k + 3)]) = 2 * (4 * k) + 5 := by
    rw [morseOut_append, morseOut_append, hU]
    top_fits
  have h23 := morseReach_trans (phaseOne_flipTail k (4 * k) hk (by omega) _ hu)
    (phaseOne_capRetract k (4 * k) hk (by omega) _ hu)
  have hwalk : morseWalk true (4 * k + 1) 4 = [(.cross true, 4 * k + 1), (.cross true, 4 * k + 2),
      (.cross true, 4 * k + 3), (.cross true, 4 * k + 4)] := rfl
  rw [phaseOneTailWalk, phaseOneTailRetracted, hwalk] at h23
  rw [phaseOneTop1, phaseOneTop2]
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h23 ⊢
  exact morseReach_trans h1 h23

/-- Level `4k - 1`: the flip up to the tail. -/
theorem phaseOne_stepS2_flip (k : ℕ) (hk : 2 ≤ k) :
    MorseReach 1 (phaseOneTop2 k) (phaseOneS2Mid k) := by
  have hk1 : 1 ≤ k := by omega
  have hb2 : morseBand (4 * k - 2) (4 * k) =
      [(.cross true, 4 * k - 1), (.cross true, 4 * k - 2), (.cross false, 4 * k - 1)] := by
    have := morseBand_two_top (4 * k - 2)
    rwa [show 4 * k - 2 + 2 = 4 * k by omega, show 4 * k - 2 + 1 = 4 * k - 1 by omega] at this
  have hcr : morseCupRun (2 * k) (4 * k) =
      morseCupRun (2 * k) (4 * k - 1) ++ [(.cup, 4 * k)] := by
    have := morseCupRun_succ (2 * k) (4 * k - 1) (by omega)
    rwa [show 4 * k - 1 + 1 = 4 * k by omega] at this
  have h1 := phaseOne_flipHead k (4 * k - 1) hk1 (by omega)
    ([(.cup, 4 * k + 2), (.cross true, 4 * k + 1), (.cross true, 4 * k),
        (.cross true, 4 * k - 1), (.cross false, 4 * k), (.cross false, 4 * k + 1)] ++
      [(.cup, 4 * k + 4), (.cross true, 4 * k + 3), (.cross false, 4 * k + 2),
        (.cross false, 4 * k + 3)] ++
      morseBand (4 * k - 2) (4 * k) ++ [(.cap, 4 * k)] ++
      morseStairRun (2 * k) (4 * k - 3) ++ morseBand 0 (2 * k + 1) ++ morseBand (2 * k) (4 * k) ++
      [(.cross true, 4 * k + 1)] ++ morseCapRun (4 * k + 1))
  rw [show 4 * k - 1 + 1 = 4 * k by omega, show 4 * k - 1 + 2 = 4 * k + 1 by omega] at h1
  have hP : morseOut 1 (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) (4 * k - 1) ++
      [(.cup, 4 * k + 1), (.cross true, 4 * k)] ++ morseBand (2 * k - 1) (4 * k)) = 8 * k + 1 := by
    rw [morseOut_append, morseOut_of_cross _ _ fun b hb ↦ (mem_morseBand (by omega) hb).1,
      morseOut_append, morseOut_head_cups k (4 * k - 1) hk1 (by omega)]
    top_fits
  have h2 := morseReach_frame 5 1 (4 * k - 2) (4 * k - 2)
    (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) (4 * k - 1) ++
      [(.cup, 4 * k + 1), (.cross true, 4 * k)] ++ morseBand (2 * k - 1) (4 * k))
    (morseStairRun (2 * k) (4 * k - 3) ++ morseBand 0 (2 * k + 1) ++ morseBand (2 * k) (4 * k) ++
      [(.cross true, 4 * k + 1)] ++ morseCapRun (4 * k + 1))
    _ _ morseReach_phaseOneMacroS2a phaseOneMacroS2a_fits (by rw [hP]; omega)
  have e2l : morseShiftWord (4 * k - 2) phaseOneMacroS2a_lhs =
      [(.cross true, 4 * k + 1)] ++
      [(.cup, 4 * k + 2), (.cross true, 4 * k + 1), (.cross true, 4 * k),
        (.cross true, 4 * k - 1), (.cross false, 4 * k), (.cross false, 4 * k + 1)] ++
      [(.cup, 4 * k + 4), (.cross true, 4 * k + 3), (.cross false, 4 * k + 2),
        (.cross false, 4 * k + 3)] ++
      [(.cross true, 4 * k - 1), (.cross true, 4 * k - 2), (.cross false, 4 * k - 1)] ++
      [(.cap, 4 * k)] := by
    simp only [phaseOneMacroS2a_lhs]; top_shift
  have e2r : morseShiftWord (4 * k - 2) phaseOneMacroS2a_rhs =
      morseShiftWord (4 * k - 2) phaseOneR2s ++ [(.cross true, 4 * k), (.cross true, 4 * k + 1),
        (.cross true, 4 * k + 2), (.cross true, 4 * k + 3)] := by
    rw [show phaseOneMacroS2a_rhs = phaseOneR2s ++ [(.cross true, 2), (.cross true, 3),
      (.cross true, 4), (.cross true, 5)] from rfl, morseShiftWord_append]
    congr 1
    top_shift
  rw [e2l, e2r] at h2
  have hwalk : morseWalk true (4 * k) 4 = [(.cross true, 4 * k), (.cross true, 4 * k + 1),
      (.cross true, 4 * k + 2), (.cross true, 4 * k + 3)] := rfl
  rw [phaseOneTop2, phaseOneS2Mid, phaseOneS2Pre, phaseOneTailWalk,
    show 4 * k - 1 + 1 = 4 * k by omega, show 4 * k - 1 - 2 = 4 * k - 3 by omega,
    show 4 * k - 1 + 2 = 4 * k + 1 by omega, hcr, hwalk]
  rw [hb2] at h1 ⊢
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
  exact morseReach_trans h1 h2

/-- Level `4k - 1`: the end of the flip and the retraction. -/
theorem phaseOne_stepS2_retract (k : ℕ) (hk : 2 ≤ k) :
    MorseReach 1 (phaseOneS2Mid k) (phaseOneStair k (4 * k - 1)) := by
  have hk1 : 1 ≤ k := by omega
  have hR : morseOut 5 phaseOneR2s = 7 ∧ morseFits 5 phaseOneR2s = true :=
    ⟨by decide, by decide⟩
  have hpre : morseOut 1 (phaseOneS2Pre k) = 2 * (4 * k - 1) + 5 := by
    have := (morseOut_fits_shift 5 (4 * k - 2) (4 * k - 2) phaseOneR2s hR.2).1
    rw [phaseOneS2Pre, morseOut_append, morseOut_append,
      morseOut_of_cross _ _ fun b hb ↦ (mem_morseBand (by omega) hb).1, morseOut_append,
      morseOut_head_cups k (4 * k - 1) hk1 (by omega),
      show morseOut (2 * (4 * k - 1) + 1) [(.cup, 4 * k + 1), (.cross true, 4 * k)] =
        4 * k - 2 + 5 + (4 * k - 2) by top_fits, this, hR.1]
    omega
  refine morseReach_trans (morseReach_trans
    (phaseOne_flipTail k (4 * k - 1) hk1 (by omega) _ hpre)
    (phaseOne_capRetract k (4 * k - 1) hk1 (by omega) _ hpre)) ?_
  have hR2s : morseShiftWord (4 * k - 2) phaseOneR2s =
      [(.cross false, 4 * k), (.cup, 4 * k + 3), (.cross true, 4 * k + 2),
        (.cross true, 4 * k + 1), (.cross true, 4 * k), (.cross true, 4 * k - 1)] ++
      [(.cross false, 4 * k), (.cross false, 4 * k + 1), (.cross false, 4 * k + 2),
        (.cup, 4 * k + 5), (.cross true, 4 * k + 4), (.cross false, 4 * k + 3),
        (.cross false, 4 * k + 4), (.cross true, 4 * k), (.cross true, 4 * k - 1),
        (.cross true, 4 * k - 2), (.cross false, 4 * k - 1), (.cross false, 4 * k),
        (.cap, 4 * k + 1)] := by
    simp only [phaseOneR2s]; top_shift
  have hM : phaseOneStairBlocks (4 * k - 2) 0 =
      [(.cup, 4 * k + 1), (.cross true, 4 * k), (.cross true, 4 * k - 1), (.cup, 4 * k),
        (.cross false, 4 * k), (.cross false, 4 * k + 1), (.cross false, 4 * k + 2),
        (.cup, 4 * k + 5), (.cross true, 4 * k + 4), (.cross false, 4 * k + 3),
        (.cross false, 4 * k + 4), (.cross true, 4 * k), (.cross true, 4 * k - 1)] := by
    simp only [phaseOneStairBlocks, List.replicate_zero, List.flatten_nil, List.append_nil,
      stripM]
    top_shift
  have hTp : morseShiftWord (4 * k - 3) phaseOneTp =
      [(.cross true, 4 * k - 2), (.cross false, 4 * k - 1), (.cross false, 4 * k),
        (.cap, 4 * k + 1), (.cross true, 4 * k - 2), (.cross true, 4 * k - 3),
        (.cross false, 4 * k - 2), (.cap, 4 * k - 1)] := by
    simp only [phaseOneTp]; top_shift
  have hb2 : morseBand (4 * k - 3) (4 * k - 1) =
      [(.cross true, 4 * k - 2), (.cross true, 4 * k - 3), (.cross false, 4 * k - 2)] := by
    have := morseBand_two_top (4 * k - 3)
    rwa [show 4 * k - 3 + 2 = 4 * k - 1 by omega, show 4 * k - 3 + 1 = 4 * k - 2 by omega] at this
  have h3 := phaseOne_retractHead k (4 * k - 1) hk1 (by omega)
    ([(.cup, 4 * k + 3), (.cross true, 4 * k + 2), (.cross true, 4 * k + 1),
        (.cross true, 4 * k), (.cross true, 4 * k - 1)] ++
      [(.cross false, 4 * k), (.cross false, 4 * k + 1), (.cross false, 4 * k + 2),
        (.cup, 4 * k + 5), (.cross true, 4 * k + 4), (.cross false, 4 * k + 3),
        (.cross false, 4 * k + 4), (.cross true, 4 * k), (.cross true, 4 * k - 1),
        (.cross true, 4 * k - 2), (.cross false, 4 * k - 1), (.cross false, 4 * k),
        (.cap, 4 * k + 1)] ++
      morseBand (4 * k - 3) (4 * k - 1) ++ [(.cap, 4 * k - 1)] ++
      morseStairRun (2 * k) (4 * k - 4) ++
      morseBand 0 (2 * k + 1) ++ morseBand (2 * k) (4 * k - 1) ++ [(.cross true, 4 * k)] ++
      morseCapRun (4 * k))
  rw [show 4 * k - 1 + 2 = 4 * k + 1 by omega, show 4 * k - 1 + 1 = 4 * k by omega] at h3
  have hU : morseOut 1 (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) (4 * k - 1) ++
      morseBand (2 * k - 1) (4 * k - 1)) = 8 * k - 1 := by
    rw [morseOut_append, morseOut_head_cups k (4 * k - 1) hk1 (by omega),
      morseOut_of_cross _ _ fun b hb ↦ (mem_morseBand (by omega) hb).1]
    omega
  have h4 := morseReach_frame 2 1 (4 * k - 1) (4 * k - 2)
    (morseHeadRun (2 * k - 1) ++ morseCupRun (2 * k) (4 * k - 1) ++
      morseBand (2 * k - 1) (4 * k - 1))
    ([(.cross false, 4 * k), (.cross false, 4 * k + 1), (.cross false, 4 * k + 2),
        (.cup, 4 * k + 5), (.cross true, 4 * k + 4), (.cross false, 4 * k + 3),
        (.cross false, 4 * k + 4), (.cross true, 4 * k), (.cross true, 4 * k - 1),
        (.cross true, 4 * k - 2), (.cross false, 4 * k - 1), (.cross false, 4 * k),
        (.cap, 4 * k + 1)] ++
      morseBand (4 * k - 3) (4 * k - 1) ++ [(.cap, 4 * k - 1)] ++
      morseStairRun (2 * k) (4 * k - 4) ++
      morseBand 0 (2 * k + 1) ++ morseBand (2 * k) (4 * k - 1) ++ [(.cross true, 4 * k)] ++
      morseCapRun (4 * k))
    _ _ morseReach_phaseOneMacroS2c phaseOneMacroS2c_fits (by rw [hU]; omega)
  have e4l : morseShiftWord (4 * k - 1) phaseOneMacroS2c_lhs =
      [(.cup, 4 * k - 1), (.cup, 4 * k + 3), (.cross true, 4 * k + 2), (.cross true, 4 * k + 1),
        (.cross true, 4 * k), (.cross true, 4 * k - 1)] := by
    simp only [phaseOneMacroS2c_lhs]; top_shift
  have e4r : morseShiftWord (4 * k - 1) phaseOneMacroS2c_rhs =
      [(.cup, 4 * k + 1), (.cross true, 4 * k), (.cross true, 4 * k - 1), (.cup, 4 * k)] := by
    simp only [phaseOneMacroS2c_rhs]; top_shift
  rw [e4l, e4r] at h4
  rw [phaseOneS2Pre, phaseOneTailRetracted, phaseOneStair, hR2s,
    show 4 * k - 1 - 1 = 4 * k - 2 by omega, show 4 * k - 1 - (4 * k - 1) = 0 by omega,
    show 4 * k - 1 - 2 = 4 * k - 3 by omega, show 4 * k - 1 - 3 = 4 * k - 4 by omega,
    show 4 * k - 1 + 1 = 4 * k by omega, hM, hTp]
  rw [hb2] at h3 h4 ⊢
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h3 h4 ⊢
  exact morseReach_trans h3 h4

end AJConjecture
