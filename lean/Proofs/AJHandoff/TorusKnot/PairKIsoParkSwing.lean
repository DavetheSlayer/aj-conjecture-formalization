import Mathlib
import AJHandoff.TorusKnot.PairKIsoCore
import AJHandoff.TorusKnot.PairKIsoCompBraid

/-!
# The companion re-closing: closures cut at a strand, and the swing of a closing arc

`pairCloseAt m k β`: the closure of the braid word `β` on `m` strands, cut open at the strand
`k`: the strands `0 … k - 1` are closed by `k` nested arcs on the left, the strands
`k + 1 … m - 1` by `m - 1 - k` nested arcs on the right, the strand `k` runs from the bottom end
to the top end. For `k = 0` it is `morseLongClosure m β`; for `m = r`, `k = r - 2`,
`β = pairRevTorusWord r s` it is `pairCore r s` (`PairKIsoCompReclose`).

`morseReach_pairCloseAt_swing` (generic in `β`): the innermost left arc (closing the strand `0`)
swings over the braid to the right, where it becomes the innermost right arc closing the strand
`m - 1`; the braid strands are relabelled cyclically, i.e. `β` is conjugated by
`δ̄ = σ_{m-2} ⋯ σ_0` (the arc's strand walks over the others at the bottom and back at the top).
Route: insert `δ̄⁻¹ δ̄` below `β` (`r2`), slide the cup of the arc across the `m - 1` strands
(`cupSlide`: `u_i x_{i+1}⁻¹ ~ u_{i+1} x_i`, once per strand), symmetrically at the cap
(`capSlide`), and one `kink` (a left arc and a right arc have rotation numbers differing by two).
Validated (`SCR/ISO2/tools/reclose.py`, `test_swing.py`): equal Kauffman bracket and writhe for
the torus words and 108 random knot-closing braids, `m = 3, 4, 5`, every `k`, both signs of the
walk.

`morseReach_pairRevTorus_conj`: `δ̄ · δ̄^s · δ̄⁻¹ ~ δ̄^s` (`r2` cancellations,
`δ̄ · δ̄^s = δ̄^s · δ̄` as lists).
-/

namespace AJConjecture

/-- The closure of `β` cut at the strand `k` (`k` arcs on the left, `m - 1 - k` on the right). -/
def pairCloseAt (m k : ℕ) (β : BraidWord) : MorseWord :=
  (List.range k).map isoU ++ (List.range (m - 1 - k)).map (fun j ↦ isoU (2 * k + 1 + j)) ++
    morseShiftWord k (morseOfBraid β) ++
    (if k = 0 then (List.range (m - 1)).reverse.map (fun j ↦ isoN (j + 1))
     else [isoN (k - 1)] ++ (List.range (m - 1 - k)).reverse.map (fun j ↦ isoN (2 * k - 1 + j)) ++
       (List.range (k - 1)).reverse.map isoN)

/-- The cyclic braid `δ̄ = σ_{m-2} ⋯ σ_0` (moves the strand `m - 1` to the position `0`). -/
def pairDeltaBar (m : ℕ) : BraidWord := (List.range (m - 1)).reverse.map fun i ↦ (i, true)

/-- A Morse word of crossings keeps the number of strands. -/
private theorem morseOut_morseOfBraid_swing (n : ℕ) (w : BraidWord) :
    morseOut n (morseOfBraid w) = n := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    simp only [morseOfBraid, List.map_cons, morseOut, morseLetterOut, morseKindOut, morseKindIn,
      Nat.add_sub_cancel] at ih ⊢
    exact ih

/-- The Morse word of a concatenation. -/
private theorem morseOfBraid_append_swing (u v : BraidWord) :
    morseOfBraid (u ++ v) = morseOfBraid u ++ morseOfBraid v := by
  simp [morseOfBraid]

/-- A braid word followed by its inverse cancels (`r2`, from the middle outwards). -/
private theorem morseReach_braid_cancel_swing (n₀ n : ℕ) (w : BraidWord) (hw : IsOnStrands n w) :
    ∀ (u v : MorseWord), n ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ morseOfBraid (w ++ isoBraidInv w) ++ v) (u ++ v) := by
  induction w with
  | nil => intro u v _; simpa [isoBraidInv, morseOfBraid] using morseReach_refl n₀ (u ++ v)
  | cons g w ih =>
    intro u v hu
    have hg := hw g List.mem_cons_self
    have h1 := ih (fun x hx ↦ hw x (List.mem_cons_of_mem _ hx)) (u ++ [(MorseKind.cross g.2, g.1)])
      ((MorseKind.cross (!g.2), g.1) :: v) (by
        rw [morseOut_append]
        simp only [morseOut, morseLetterOut, morseKindOut, morseKindIn, Nat.add_sub_cancel]
        exact hu)
    have h2 := morseReach_isoRule n₀ u v (.r2 g.1 g.2) rfl
      (by
        simp only [morseRuleLhs, morseFits_cons, morseKindIn, morseLetterOut, morseKindOut,
          Nat.add_sub_cancel, morseFits_nil, and_true]
        omega) rfl
    have he : morseOfBraid (g :: w ++ isoBraidInv (g :: w)) =
        (MorseKind.cross g.2, g.1) :: (morseOfBraid (w ++ isoBraidInv w) ++
          [(MorseKind.cross (!g.2), g.1)]) := by
      simp [morseOfBraid, isoBraidInv]
    rw [he]
    simp only [morseRuleLhs, morseRuleRhs, List.append_nil, List.append_assoc, List.cons_append,
      List.nil_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- A rightward walk grows at its end. -/
private theorem morseWalk_succ_swing (s : Bool) (p len : ℕ) :
    morseWalk s p (len + 1) = morseWalk s p len ++ [(MorseKind.cross s, p + len)] := by
  simp [morseWalk, List.range_succ]

/-- A rightward walk starts with its first crossing. -/
private theorem morseWalk_succ_head_swing (s : Bool) (p len : ℕ) :
    morseWalk s p (len + 1) = (MorseKind.cross s, p) :: morseWalk s (p + 1) len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    rw [morseWalk_succ_swing, ih, morseWalk_succ_swing]
    simp only [List.cons_append, List.cons.injEq, List.append_cancel_left_eq, Prod.mk.injEq,
      true_and, and_true]
    omega

/-- A leftward walk grows at its front. -/
private theorem morseWalkL_succ_swing (s : Bool) (p len : ℕ) :
    morseWalkL s p (len + 1) = (MorseKind.cross s, p + len) :: morseWalkL s p len := by
  simp [morseWalkL, List.range_succ]

/-- A leftward walk ends with its last crossing. -/
private theorem morseWalkL_succ_last_swing (s : Bool) (p len : ℕ) :
    morseWalkL s p (len + 1) = morseWalkL s (p + 1) len ++ [(MorseKind.cross s, p)] := by
  induction len with
  | zero => rfl
  | succ len ih =>
    rw [morseWalkL_succ_swing, ih, morseWalkL_succ_swing]
    simp only [List.cons_append, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    omega

/-- The letters of a leftward walk. -/
private theorem mem_morseWalkL_swing {s : Bool} {p len : ℕ} {b : MorseLetter}
    (hb : b ∈ morseWalkL s p len) : b.1 = MorseKind.cross s ∧ p ≤ b.2 ∧ b.2 + 1 ≤ p + len := by
  simp only [morseWalkL, List.mem_map, List.mem_reverse, List.mem_range] at hb
  obtain ⟨i, hi, rfl⟩ := hb
  exact ⟨rfl, by simp only; omega, by simp only; omega⟩

/-- A leftward walk keeps the number of strands. -/
private theorem morseOut_morseWalkL_swing (n : ℕ) (s : Bool) (p len : ℕ) :
    morseOut n (morseWalkL s p len) = n :=
  morseOut_of_cross n _ fun _ hb ↦ ⟨s, (mem_morseWalkL_swing hb).1⟩

/-- A walk and the reversed walk of the opposite sign cancel (`r2`, from the middle). -/
private theorem morseReach_walk_cancel_swing (n₀ p : ℕ) (s : Bool) :
    ∀ (len : ℕ) (u v : MorseWord), p + len + 1 ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ morseWalk s p len ++ morseWalkL (!s) p len ++ v) (u ++ v)
  | 0, u, v, _ => by simpa [morseWalk, morseWalkL] using morseReach_refl n₀ (u ++ v)
  | len + 1, u, v, hu => by
    have h1 := morseReach_isoRule n₀ (u ++ morseWalk s p len) (morseWalkL (!s) p len ++ v)
      (.r2 (p + len) s) rfl
      (by
        rw [morseOut_append, morseOut_morseWalk]
        simp only [morseRuleLhs, morseFits_cons, morseKindIn, morseLetterOut, morseKindOut,
          Nat.add_sub_cancel, morseFits_nil, and_true]
        omega) rfl
    have h2 := morseReach_walk_cancel_swing n₀ p s len u v (by omega)
    rw [morseWalk_succ_swing, morseWalkL_succ_swing]
    simp only [morseRuleLhs, morseRuleRhs, List.append_nil, List.append_assoc, List.cons_append,
      List.nil_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- A bead on one strand travels along a rightward walk. -/
private theorem morseReach_bead_walk_swing (n₀ : ℕ) (T : MorseWord) (hT : morseFits 1 T = true)
    (hTo : morseOut 1 T = 1) (s : Bool) :
    ∀ (len p : ℕ) (u v : MorseWord), p + len + 1 ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ morseShiftWord p T ++ morseWalk s p len ++ v)
        (u ++ morseWalk s p len ++ morseShiftWord (p + len) T ++ v)
  | 0, p, u, v, _ => by simpa [morseWalk] using morseReach_refl n₀ (u ++ morseShiftWord p T ++ v)
  | len + 1, p, u, v, hu => by
    have h1 := morseReach_passL n₀ p 1 s u T (morseWalk s (p + 1) len ++ v) hT (by omega)
      (by rw [hTo]; omega)
    have h2 := morseReach_bead_walk_swing n₀ T hT hTo s len (p + 1)
      (u ++ [(MorseKind.cross s, p)]) v (by
        rw [morseOut_append]
        simp only [morseOut, morseLetterOut, morseKindOut, morseKindIn, Nat.add_sub_cancel]
        omega)
    rw [hTo] at h1
    rw [morseWalk_succ_head_swing, show p + (len + 1) = p + 1 + len by omega]
    simp only [morseWalkL, List.range_one, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.map_cons, List.map_nil, Nat.add_zero, List.append_assoc, List.cons_append,
      List.nil_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- A bead on one strand travels along a leftward walk. -/
private theorem morseReach_bead_walkL_swing (n₀ : ℕ) (T : MorseWord) (hT : morseFits 1 T = true)
    (hTo : morseOut 1 T = 1) (s : Bool) :
    ∀ (len p : ℕ) (u v : MorseWord), p + len + 1 ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ morseShiftWord (p + len) T ++ morseWalkL s p len ++ v)
        (u ++ morseWalkL s p len ++ morseShiftWord p T ++ v)
  | 0, p, u, v, _ => by simpa [morseWalkL] using morseReach_refl n₀ (u ++ morseShiftWord p T ++ v)
  | len + 1, p, u, v, hu => by
    have h1 := morseReach_symm (morseReach_pass n₀ (p + len) 1 s u T
      (morseWalkL s p len ++ v) hT (by omega))
    have h2 := morseReach_bead_walkL_swing n₀ T hT hTo s len p
      (u ++ [(MorseKind.cross s, p + len)]) v (by
        rw [morseOut_append]
        simp only [morseOut, morseLetterOut, morseKindOut, morseKindIn, Nat.add_sub_cancel]
        omega)
    rw [hTo] at h1
    rw [morseWalkL_succ_swing, show p + (len + 1) = p + len + 1 by omega]
    simp only [morseWalk, List.range_one, List.map_cons, List.map_nil, Nat.add_zero,
      List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- Shifts compose. -/
private theorem morseShiftWord_shift_swing (a b : ℕ) (w : MorseWord) :
    morseShiftWord a (morseShiftWord b w) = morseShiftWord (b + a) w := by
  simp only [morseShiftWord, List.map_map]
  refine List.map_congr_left fun l _ ↦ ?_
  simp only [Function.comp_apply, shiftLetter, Prod.mk.injEq, true_and]
  omega

/-- A twisted cup is a cup with a positive right curl on its right leg (fixed macro). -/
private theorem morseReach_twistCup_swing (n₀ a : ℕ) (u v : MorseWord)
    (hu : a ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ [isoU a, isoX false a] ++ v)
      (u ++ [isoU a] ++ morseShiftWord (a + 1) (isoCurlR true 0) ++ v) := by
  have h0 : MorseReach 0 [isoU 0, isoX false 0] ([isoU 0] ++ morseShiftWord 1 (isoCurlR true 0)) :=
    ⟨[(1, .zig 1 true, true), (1, .cupSlide 0 true false, true),
      (0, .exch (.cup, 0) (.cup, 0), true), (4, .exch (.cross false, 0) (.cap, 2), true),
      (3, .r2 0 true, false)], by decide⟩
  have h := morseReach_frame 0 n₀ a (morseOut n₀ u - a) u v _ _ h0 (by decide) (by omega)
  rw [morseShiftWord_append, morseShiftWord_shift_swing, Nat.add_comm 1 a] at h
  simpa only [morseShiftWord, shiftLetter, isoU, isoX, List.map_cons, List.map_nil,
    Nat.zero_add, List.append_assoc] using h

/-- A positive right curl before a twisted cap cancels it (fixed macro, one `kink`). -/
private theorem morseReach_twistCap_swing (n₀ a : ℕ) (u v : MorseWord)
    (hu : a + 2 ≤ morseOut n₀ u) :
    MorseReach n₀ (u ++ morseShiftWord (a + 1) (isoCurlR true 0) ++ [isoX true a, isoN a] ++ v)
      (u ++ [isoN a] ++ v) := by
  have h0 : MorseReach 2 (morseShiftWord 1 (isoCurlR true 0) ++ [isoX true 0, isoN 0])
      [isoN 0] :=
    ⟨[(3, .zig 0 false, true), (4, .exch (.cap, 0) (.cross true, 2), false),
      (5, .exch (.cap, 0) (.cap, 2), false), (5, .r2 1 true, true),
      (3, .cupSlide 1 true false, false), (0, .kink 1 true, false)], by decide⟩
  have h := morseReach_frame 2 n₀ a (morseOut n₀ u - a - 2) u v _ _ h0 (by decide) (by omega)
  rw [morseShiftWord_append, morseShiftWord_shift_swing, Nat.add_comm 1 a] at h
  simpa only [morseShiftWord, shiftLetter, isoN, isoX, List.map_cons, List.map_nil,
    Nat.zero_add, List.append_assoc] using h

/-- A braid word on `n` strands fits on `n` strands as a Morse word. -/
private theorem morseFits_morseOfBraid_swing {n : ℕ} {w : BraidWord} (hw : IsOnStrands n w) :
    morseFits n (morseOfBraid w) = true := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    have hg := hw g List.mem_cons_self
    have ih' := ih fun x hx ↦ hw x (List.mem_cons_of_mem _ hx)
    simp only [morseOfBraid, List.map_cons, morseFits_cons] at ih' ⊢
    refine ⟨by simp only [morseKindIn]; omega, ?_⟩
    simpa only [morseLetterOut, morseKindOut, morseKindIn, Nat.add_sub_cancel] using ih'

/-- The core of the swing: the left leg of the arc passes the braid (`morseReach_pass`), the
twisted cup becomes a curl, the curl travels along the arc and cancels the twisted cap. -/
private theorem morseReach_swing_core (n₀ a m e : ℕ) (β : BraidWord) (hβ : IsOnStrands (m + 1) β)
    (u v : MorseWord) (hu : morseOut n₀ u = a + m + e) :
    MorseReach n₀ (u ++ [isoU a] ++ morseShiftWord (a + 1) (morseOfBraid β) ++ [isoN a] ++ v)
      (u ++ [isoU a] ++ morseWalk false (a + 1) m ++ morseShiftWord a (morseOfBraid β) ++
        morseWalkL true (a + 1) m ++ [isoN a] ++ v) := by
  set B := morseOfBraid β with hBdef
  set C := isoCurlR true 0 with hCdef
  have hBf : morseFits (m + 1) B = true := morseFits_morseOfBraid_swing hβ
  have hBo : morseOut (m + 1) B = m + 1 :=
    morseOut_of_cross _ _ fun b hb ↦ by
      simp only [hBdef, morseOfBraid, List.mem_map] at hb
      obtain ⟨g, -, rfl⟩ := hb
      exact ⟨g.2, rfl⟩
  have hCf : morseFits 1 C = true := by decide
  have hCo : morseOut 1 C = 1 := by decide
  have hu1 : morseOut n₀ (u ++ [isoU a]) = a + m + 2 + e := by
    rw [morseOut_append, hu]
    simp only [isoU, morseOut, morseLetterOut, morseKindOut, morseKindIn]
    omega
  have hwo : ∀ (x : MorseWord) s p len, morseOut n₀ (x ++ morseWalk s p len) = morseOut n₀ x :=
    fun x s p len ↦ by rw [morseOut_append, morseOut_morseWalk]
  -- pass and cancel
  have s1 := morseReach_pass n₀ a (m + 1) false (u ++ [isoU a]) B
    (morseWalkL true a (m + 1) ++ [isoN a] ++ v) hBf (by rw [hu1]; omega)
  rw [hBo] at s1
  have hsc : ∀ d n, morseOut n (morseShiftWord d B) = n := fun d n ↦
    morseOut_of_cross _ _ fun b hb ↦ by
      simp only [morseShiftWord, hBdef, morseOfBraid, List.map_map, List.mem_map] at hb
      obtain ⟨g, -, rfl⟩ := hb
      exact ⟨g.2, rfl⟩
  have s2 := morseReach_walk_cancel_swing n₀ a false (m + 1)
    (u ++ [isoU a] ++ morseShiftWord (a + 1) B) ([isoN a] ++ v)
    (by rw [morseOut_append, hu1, hsc]; omega)
  -- the twisted cup becomes a curl
  have s3 := morseReach_twistCup_swing n₀ a u
    (morseWalk false (a + 1) m ++ morseShiftWord a B ++ morseWalkL true a (m + 1) ++ [isoN a] ++ v)
    (by omega)
  -- the curl travels along the walk
  have s4 := morseReach_bead_walk_swing n₀ C hCf hCo false m (a + 1) (u ++ [isoU a])
    (morseShiftWord a B ++ morseWalkL true a (m + 1) ++ [isoN a] ++ v) (by rw [hu1]; omega)
  -- the curl passes the braid
  have s5 := morseReach_comm n₀ (u ++ [isoU a] ++ morseWalk false (a + 1) m)
    (morseShiftWord a B) (morseShiftWord (a + 1 + m) C)
    (morseWalkL true a (m + 1) ++ [isoN a] ++ v)
    (fun b hb ↦ by
      simp only [morseShiftWord, hBdef, morseOfBraid, List.map_map, List.mem_map] at hb
      obtain ⟨g, -, rfl⟩ := hb
      exact ⟨g.2, rfl⟩)
    (fun b hb c hc ↦ by
      simp only [morseShiftWord, hBdef, morseOfBraid, List.map_map, List.mem_map] at hb
      obtain ⟨g, hg, rfl⟩ := hb
      have := hβ g hg
      simp only [hCdef, isoCurlR, isoU, isoX, isoN, morseShiftWord, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;> simp only [Function.comp_apply, shiftLetter] <;> omega)
    (by
      rw [hwo, hu1, morseFits_append]
      have hC := morseFits_morseShiftWord 1 (a + 1 + m) e C hCf
      rw [show 1 + (a + 1 + m) + e = a + m + 2 + e by omega] at hC
      have hCo' : ∀ d n, morseOut n (morseShiftWord d C) = n := fun d n ↦ by
        simp only [hCdef, isoCurlR, isoU, isoX, isoN, morseShiftWord, List.map_cons,
          List.map_nil, shiftLetter, morseOut, morseLetterOut, morseKindOut, morseKindIn]
        omega
      have hB := morseFits_morseShiftWord (m + 1) a (e + 1) B hBf
      rw [show m + 1 + a + (e + 1) = a + m + 2 + e by omega] at hB
      rw [hC, hCo', hB, Bool.true_and])
  -- the curl travels back along the leftward walk
  have s6 := morseReach_bead_walkL_swing n₀ C hCf hCo true m (a + 1)
    (u ++ [isoU a] ++ morseWalk false (a + 1) m ++ morseShiftWord a B)
    ([isoX true a, isoN a] ++ v) (by rw [morseOut_append, hsc, hwo, hu1]; omega)
  -- the curl cancels the twisted cap
  have s7 := morseReach_twistCap_swing n₀ a
    (u ++ [isoU a] ++ morseWalk false (a + 1) m ++ morseShiftWord a B ++
      morseWalkL true (a + 1) m) v
    (by rw [morseOut_append, morseOut_morseWalkL_swing, morseOut_append, hsc, hwo, hu1]; omega)
  rw [morseWalk_succ_head_swing, morseWalkL_succ_last_swing] at s1 s2
  rw [morseWalkL_succ_last_swing] at s3 s4 s5
  rw [← hCdef] at s3 s7
  simp only [Bool.not_false, isoX, List.append_assoc, List.cons_append,
    List.nil_append] at s1 s2 s3 s4 s5 s6 s7 ⊢
  exact morseReach_trans (morseReach_symm s2) (morseReach_trans (morseReach_symm s1)
    (morseReach_trans s3 (morseReach_trans s4 (morseReach_trans s5 (morseReach_trans s6 s7)))))

/-- A cup on the right whose left leg walks left is a cup on the left whose right leg walks right
(`cupSlide` and `r2` per strand). -/
private theorem morseReach_cup_walk_swing (n₀ a : ℕ) :
    ∀ (len : ℕ) (u v : MorseWord), a + len ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ [isoU (a + len)] ++ morseWalkL true a len ++ v)
        (u ++ [isoU a] ++ morseWalk false (a + 1) len ++ v)
  | 0, u, v, _ => by simpa [morseWalk, morseWalkL] using morseReach_refl n₀ (u ++ [isoU a] ++ v)
  | len + 1, u, v, hu => by
    have h0 : MorseReach 1 [isoU 1, isoX true 0] [isoU 0, isoX false 1] :=
      ⟨[(0, .cupSlide 0 false false, true), (2, .r2 0 false, false)], by decide⟩
    have h1 := morseReach_frame 1 n₀ (a + len) (morseOut n₀ u - (a + len + 1)) u
      (morseWalkL true a len ++ v) _ _ h0 (by decide) (by omega)
    simp only [morseShiftWord, shiftLetter, isoU, isoX, List.map_cons, List.map_nil,
      Nat.zero_add, show 1 + (a + len) = a + len + 1 by omega] at h1
    have h2 := morseReach_comm n₀ (u ++ [isoU (a + len)]) (morseWalkL true a len)
      [isoX false (a + len + 1)] v (fun b hb ↦ ⟨true, (mem_morseWalkL_swing hb).1⟩)
      (fun b hb c hc ↦ by
        have := mem_morseWalkL_swing hb
        rw [List.mem_singleton] at hc
        subst hc
        simp only [isoX]
        omega)
      (by
        rw [morseOut_append]
        simp only [isoU, isoX, List.singleton_append, morseOut, morseLetterOut, morseKindOut,
          morseKindIn, morseFits_cons]
        refine ⟨by omega, morseFits_of_cross _ _ (fun b hb ↦ ⟨true, (mem_morseWalkL_swing hb).1⟩)
          fun b hb ↦ ?_⟩
        have := mem_morseWalkL_swing hb
        omega)
    have h3 := morseReach_cup_walk_swing n₀ a len u ([isoX false (a + len + 1)] ++ v) (by omega)
    rw [morseWalkL_succ_swing, morseWalk_succ_swing, show a + (len + 1) = a + len + 1 by omega,
      show a + 1 + len = a + len + 1 by omega]
    simp only [isoU, isoX, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- A walk ending at the left leg of a cap: the cap moves to the left (`capSlide` and `r2` per
strand). -/
private theorem morseReach_cap_walk_swing (n₀ a : ℕ) :
    ∀ (len : ℕ) (u v : MorseWord), a + len + 2 ≤ morseOut n₀ u →
      MorseReach n₀ (u ++ morseWalk false a len ++ [isoN (a + len)] ++ v)
        (u ++ morseWalkL true (a + 1) len ++ [isoN a] ++ v)
  | 0, u, v, _ => by simpa [morseWalk, morseWalkL] using morseReach_refl n₀ (u ++ [isoN a] ++ v)
  | len + 1, u, v, hu => by
    have h0 : MorseReach 3 [isoX false 0, isoN 1] [isoX true 1, isoN 0] :=
      ⟨[(1, .capSlide 0 true true, true), (0, .r2 0 false, false)], by decide⟩
    have hw : morseOut n₀ (u ++ morseWalk false a len) = morseOut n₀ u := by
      rw [morseOut_append, morseOut_morseWalk]
    have h1 := morseReach_frame 3 n₀ (a + len) (morseOut n₀ u - (a + len + 3))
      (u ++ morseWalk false a len) v _ _ h0 (by decide) (by omega)
    simp only [morseShiftWord, shiftLetter, isoN, isoX, List.map_cons, List.map_nil,
      Nat.zero_add, show 1 + (a + len) = a + len + 1 by omega] at h1
    have h2 := morseReach_symm (morseReach_comm n₀ u (morseWalk false a len)
      [isoX true (a + len + 1)] ([isoN (a + len)] ++ v)
      (fun b hb ↦ ⟨false, (mem_morseWalk hb).1⟩)
      (fun b hb c hc ↦ by
        have := mem_morseWalk hb
        rw [List.mem_singleton] at hc
        subst hc
        simp only [isoX]
        omega)
      (by
        simp only [isoX, List.singleton_append, morseFits_cons, morseLetterOut, morseKindOut,
          morseKindIn, Nat.add_sub_cancel]
        refine ⟨by omega, morseFits_of_cross _ _ (fun b hb ↦ ⟨false, (mem_morseWalk hb).1⟩)
          fun b hb ↦ ?_⟩
        have := mem_morseWalk hb
        omega))
    have h3 := morseReach_cap_walk_swing n₀ a len (u ++ [isoX true (a + len + 1)]) v (by
      rw [morseOut_append]
      simp only [isoX, morseOut, morseLetterOut, morseKindOut, morseKindIn, Nat.add_sub_cancel]
      omega)
    rw [morseWalk_succ_swing, morseWalkL_succ_swing, show a + (len + 1) = a + len + 1 by omega,
      show a + 1 + len = a + len + 1 by omega]
    simp only [isoN, isoX, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 h3 ⊢
    exact morseReach_trans h1 (morseReach_trans h2 h3)

/-- The cup of the innermost left arc passes the cups of the right arcs. -/
private theorem morseReach_cup_sweep_swing (n₀ a : ℕ) :
    ∀ (b : ℕ) (u v : MorseWord), morseOut n₀ u = 2 * a + 1 →
      MorseReach n₀ (u ++ [isoU a] ++ (List.range b).map (fun j ↦ isoU (2 * a + 3 + j)) ++ v)
        (u ++ (List.range b).map (fun j ↦ isoU (2 * a + 1 + j)) ++ [isoU a] ++ v)
  | 0, u, v, _ => by simpa using morseReach_refl n₀ (u ++ [isoU a] ++ v)
  | b + 1, u, v, hu => by
    have h1 := morseReach_cup_sweep_swing n₀ a b u ([isoU (2 * a + 3 + b)] ++ v) hu
    have hout : morseOut n₀ (u ++ (List.range b).map (fun j ↦ isoU (2 * a + 1 + j))) =
        2 * a + 1 + 2 * b := by
      rw [morseOut_append, hu]
      clear h1 hu
      induction b with
      | zero => rfl
      | succ b ih =>
        rw [List.range_succ, List.map_append, morseOut_append, ih]
        simp only [isoU, List.map_cons, List.map_nil, morseOut, morseLetterOut, morseKindOut,
          morseKindIn]
        omega
    have h2 := morseReach_isoRule n₀ (u ++ (List.range b).map (fun j ↦ isoU (2 * a + 1 + j))) v
      (.exch (.cup, a) (.cup, 2 * a + 1 + b))
      (by simp only [morseRuleOk]; exact decide_eq_true (by simp only [morseKindIn]; omega))
      (by
        rw [hout]
        simp only [morseRuleLhs, morseFits_cons, morseKindIn, morseKindOut, morseLetterOut,
          morseFits_nil, and_true]
        omega)
      (by
        rw [hout]
        simp only [morseRuleRhs, morseFits_cons, morseKindIn, morseKindOut, morseLetterOut,
          morseFits_nil, and_true]
        omega)
    simp only [morseRuleLhs, morseRuleRhs, morseKindIn, morseKindOut,
      show 2 * a + 1 + b + 2 - 0 = 2 * a + 3 + b by omega] at h2
    rw [List.range_succ, List.map_append, List.map_append]
    simp only [isoU, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- The cap of the innermost left arc passes the caps of the right arcs. -/
private theorem morseReach_cap_sweep_swing (n₀ c : ℕ) :
    ∀ (b : ℕ) (u v : MorseWord), morseOut n₀ u = 2 * c + 2 * b + 5 →
      MorseReach n₀
        (u ++ [isoN c] ++ (List.range (b + 1)).reverse.map (fun j ↦ isoN (2 * c + 1 + j)) ++ v)
        (u ++ (List.range (b + 1)).reverse.map (fun j ↦ isoN (2 * c + 3 + j)) ++ [isoN c] ++ v)
  | 0, u, v, hu => by
    have h := morseReach_isoRule n₀ u v (.exch (.cap, c) (.cap, 2 * c + 3))
      (by simp only [morseRuleOk]; exact decide_eq_true (by simp only [morseKindIn]; omega))
      (by
        rw [hu]
        simp only [morseRuleLhs, morseFits_cons, morseKindIn, morseKindOut, morseLetterOut,
          morseFits_nil, and_true]
        omega)
      (by
        rw [hu]
        simp only [morseRuleRhs, morseFits_cons, morseKindIn, morseKindOut, morseLetterOut,
          morseFits_nil, and_true]
        omega)
    simp only [morseRuleLhs, morseRuleRhs, morseKindIn, morseKindOut,
      show 2 * c + 3 + 0 - 2 = 2 * c + 1 by omega] at h
    simpa [isoN] using h
  | b + 1, u, v, hu => by
    have h1 := morseReach_isoRule n₀ u
      ((List.range (b + 1)).reverse.map (fun j ↦ isoN (2 * c + 1 + j)) ++ v)
      (.exch (.cap, c) (.cap, 2 * c + 3 + (b + 1)))
      (by simp only [morseRuleOk]; exact decide_eq_true (by simp only [morseKindIn]; omega))
      (by
        rw [hu]
        simp only [morseRuleLhs, morseFits_cons, morseKindIn, morseKindOut, morseLetterOut,
          morseFits_nil, and_true]
        omega)
      (by
        rw [hu]
        simp only [morseRuleRhs, morseFits_cons, morseKindIn, morseKindOut, morseLetterOut,
          morseFits_nil, and_true]
        omega)
    simp only [morseRuleLhs, morseRuleRhs, morseKindIn, morseKindOut,
      show 2 * c + 3 + (b + 1) + 0 - 2 = 2 * c + 1 + (b + 1) by omega] at h1
    have h2 := morseReach_cap_sweep_swing n₀ c b (u ++ [isoN (2 * c + 3 + (b + 1))]) v (by
      rw [morseOut_append, hu]
      simp only [isoN, morseOut, morseLetterOut, morseKindOut, morseKindIn]
      omega)
    have hrev : ∀ (f : ℕ → MorseLetter) (n : ℕ),
        (List.range (n + 1)).reverse.map f = f n :: (List.range n).reverse.map f := fun f n ↦ by
      simp [List.range_succ]
    rw [hrev _ (b + 1), hrev _ (b + 1)]
    simp only [isoN, List.append_assoc, List.cons_append, List.nil_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- The innermost left arc swings to the right (generic in the braid). -/
theorem morseReach_pairCloseAt_swing (m k : ℕ) (β : BraidWord) (hk : 1 ≤ k) (hkm : k + 1 ≤ m)
    (hβ : IsOnStrands m β) :
    MorseReach 1 (pairCloseAt m k β)
      (pairCloseAt m (k - 1) (pairDeltaBar m ++ β ++ isoBraidInv (pairDeltaBar m))) := by
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, m = a + b + 2 := ⟨m - a - 2, by omega⟩
  have e3 : a + b + 2 - 1 = a + b + 1 := by omega
  have f1 : a + b + 1 - (a + 1) = b := by omega
  have f2 : a + b + 1 - a = b + 1 := by omega
  have f3 : 2 * (a + 1) - 1 = 2 * a + 1 := by omega
  have hD1 : morseShiftWord a (morseOfBraid (pairDeltaBar (a + b + 2))) =
      morseWalkL true a (a + b + 1) := by
    simp only [morseShiftWord, morseOfBraid, pairDeltaBar, morseWalkL, List.map_map, e3]
    refine List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp_apply, shiftLetter, Prod.mk.injEq, true_and]
    omega
  have hD2 : morseShiftWord a (morseOfBraid (isoBraidInv (pairDeltaBar (a + b + 2)))) =
      morseWalk false a (a + b + 1) := by
    simp only [morseShiftWord, morseOfBraid, isoBraidInv, pairDeltaBar, morseWalk, List.map_map,
      List.map_reverse, List.reverse_reverse, e3]
    refine List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp_apply, shiftLetter, Bool.not_true, Prod.mk.injEq, true_and]
    omega
  have hU : (fun j ↦ isoU (2 * (a + 1) + 1 + j)) = fun j ↦ isoU (2 * a + 3 + j) := by
    funext j
    rw [show 2 * (a + 1) + 1 + j = 2 * a + 3 + j by omega]
  simp only [pairCloseAt, e3, f1, f2, f3, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ↓reduceIte, morseOfBraid_append_swing, morseShiftWord_append, hD1, hD2, Nat.add_sub_cancel,
    hU]
  have hCaps : ∀ W : MorseWord, morseOut 1 W = 2 * a + 2 * b + 3 →
      MorseReach 1 (W ++ (if a = 0 then (List.range (a + b + 1)).reverse.map (fun j ↦ isoN (j + 1))
        else [isoN (a - 1)] ++ (List.range (b + 1)).reverse.map (fun j ↦ isoN (2 * a - 1 + j)) ++
          (List.range (a - 1)).reverse.map isoN))
        (W ++ ([isoN (a + (a + b + 1))] ++
          (List.range b).reverse.map (fun j ↦ isoN (2 * a + 1 + j)) ++
          (List.range a).reverse.map isoN)) := by
    have hrev : ∀ (f : ℕ → MorseLetter) (n : ℕ),
        (List.range (n + 1)).reverse.map f = f n :: (List.range n).reverse.map f := fun f n ↦ by
      simp [List.range_succ]
    intro W hW
    cases a with
    | zero =>
      simp only [↓reduceIte, Nat.zero_add, hrev _ b, Nat.mul_zero, List.range_zero,
        List.reverse_nil, List.map_nil, List.append_nil, isoN, List.singleton_append]
      have hf : (fun j : ℕ ↦ ((MorseKind.cap, j + 1) : MorseLetter)) =
          fun j ↦ (MorseKind.cap, 1 + j) := funext fun j ↦ by rw [Nat.add_comm]
      rw [hf]
      exact morseReach_refl 1 _
    | succ c =>
      have h := morseReach_cap_sweep_swing 1 c b W ((List.range c).reverse.map isoN) (by omega)
      have hf1 : (fun j ↦ isoN (2 * (c + 1) - 1 + j)) = fun j ↦ isoN (2 * c + 1 + j) :=
        funext fun j ↦ by rw [show 2 * (c + 1) - 1 + j = 2 * c + 1 + j by omega]
      have hf2 : (fun j ↦ isoN (2 * (c + 1) + 1 + j)) = fun j ↦ isoN (2 * c + 3 + j) :=
        funext fun j ↦ by rw [show 2 * (c + 1) + 1 + j = 2 * c + 3 + j by omega]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, hf1, hf2, hrev,
        show c + 1 + (c + 1 + b + 1) = 2 * c + 3 + b by omega, List.append_assoc,
        List.cons_append, List.nil_append] at h ⊢
      exact h
  have hcups : ∀ (n : ℕ) (L : List ℕ) (f : ℕ → MorseLetter), (∀ j, (f j).1 = MorseKind.cup) →
      morseOut n (L.map f) = n + 2 * L.length := by
    intro n L f hf
    induction L generalizing n with
    | nil => rfl
    | cons x L ih =>
      simp only [List.map_cons, morseOut, List.length_cons, morseLetterOut, hf, morseKindOut,
        morseKindIn]
      rw [ih]
      omega
  have hP : morseOut 1 ((List.range a).map isoU) = 2 * a + 1 := by
    rw [hcups 1 _ _ fun _ ↦ rfl, List.length_range]
    omega
  have hPR : morseOut 1 ((List.range a).map isoU ++
      (List.range b).map (fun j ↦ isoU (2 * a + 1 + j))) = a + (a + b + 1) + b := by
    rw [morseOut_append, hP, hcups _ _ _ fun _ ↦ rfl, List.length_range]
    omega
  have hβ' : IsOnStrands (a + b + 1 + 1) β := hβ
  have hsc : ∀ d n, morseOut n (morseShiftWord d (morseOfBraid β)) = n := fun d n ↦
    morseOut_of_cross _ _ fun b hb ↦ by
      simp only [morseShiftWord, morseOfBraid, List.map_map, List.mem_map] at hb
      obtain ⟨g, -, rfl⟩ := hb
      exact ⟨g.2, rfl⟩
  have L1 := morseReach_cup_sweep_swing 1 a b ((List.range a).map isoU)
    (morseShiftWord (a + 1) (morseOfBraid β) ++ ([isoN a] ++
      (List.range b).reverse.map (fun j ↦ isoN (2 * a + 1 + j)) ++
      (List.range a).reverse.map isoN)) hP
  have L2 := morseReach_swing_core 1 a (a + b + 1) b β hβ'
    ((List.range a).map isoU ++ (List.range b).map (fun j ↦ isoU (2 * a + 1 + j)))
    ((List.range b).reverse.map (fun j ↦ isoN (2 * a + 1 + j)) ++
      (List.range a).reverse.map isoN) hPR
  have R1 := morseReach_cup_walk_swing 1 a (a + b + 1)
    ((List.range a).map isoU ++ (List.range b).map (fun j ↦ isoU (2 * a + 1 + j)))
    (morseShiftWord a (morseOfBraid β) ++ morseWalk false a (a + b + 1) ++
      (if a = 0 then (List.range (a + b + 1)).reverse.map (fun j ↦ isoN (j + 1))
        else [isoN (a - 1)] ++ (List.range (b + 1)).reverse.map (fun j ↦ isoN (2 * a - 1 + j)) ++
          (List.range (a - 1)).reverse.map isoN)) (by omega)
  have hM : morseOut 1 ((List.range a).map isoU ++
      (List.range b).map (fun j ↦ isoU (2 * a + 1 + j)) ++ [isoU a] ++
      morseWalk false (a + 1) (a + b + 1) ++ morseShiftWord a (morseOfBraid β)) =
      2 * a + 2 * b + 3 := by
    rw [morseOut_append, hsc, morseOut_append, morseOut_morseWalk, morseOut_append, hPR]
    simp only [isoU, morseOut, morseLetterOut, morseKindOut, morseKindIn]
    omega
  have R2 := hCaps (((List.range a).map isoU ++
      (List.range b).map (fun j ↦ isoU (2 * a + 1 + j)) ++ [isoU a] ++
      morseWalk false (a + 1) (a + b + 1) ++ morseShiftWord a (morseOfBraid β)) ++
      morseWalk false a (a + b + 1)) (by rw [morseOut_append, morseOut_morseWalk, hM])
  have R3 := morseReach_cap_walk_swing 1 a (a + b + 1)
    ((List.range a).map isoU ++ (List.range b).map (fun j ↦ isoU (2 * a + 1 + j)) ++ [isoU a] ++
      morseWalk false (a + 1) (a + b + 1) ++ morseShiftWord a (morseOfBraid β))
    ((List.range b).reverse.map (fun j ↦ isoN (2 * a + 1 + j)) ++
      (List.range a).reverse.map isoN) (by rw [hM]; omega)
  have hRc : (List.range (b + 1)).map (fun j ↦ isoU (2 * a + 1 + j)) =
      (List.range b).map (fun j ↦ isoU (2 * a + 1 + j)) ++ [isoU (a + (a + b + 1))] := by
    rw [List.range_succ, List.map_append, List.map_singleton,
      show 2 * a + 1 + b = a + (a + b + 1) by omega]
  rw [List.range_succ (n := a), List.map_append, hRc]
  simp only [List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append] at L1 L2 R1 R2 R3 ⊢
  exact morseReach_trans L1 (morseReach_trans L2
    (morseReach_symm (morseReach_trans R1 (morseReach_trans R2 R3))))

/-- Conjugating `δ̄^s` by `δ̄` gives `δ̄^s` back. -/
theorem morseReach_pairRevTorus_conj (r s : ℕ) (hr : 2 ≤ r) :
    MorseReach r (morseOfBraid (pairDeltaBar r ++ pairRevTorusWord r s ++
        isoBraidInv (pairDeltaBar r)))
      (morseOfBraid (pairRevTorusWord r s)) := by
  have hD : IsOnStrands r (pairDeltaBar r) := fun g hg ↦ by
    simp only [pairDeltaBar, List.mem_map, List.mem_reverse, List.mem_range] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    dsimp only
    omega
  have hc : pairDeltaBar r ++ pairRevTorusWord r s = pairRevTorusWord r s ++ pairDeltaBar r := by
    simp only [pairRevTorusWord, pairDeltaBar]
    rw [← List.flatten_cons, ← List.replicate_succ, List.replicate_succ', List.flatten_append,
      List.flatten_singleton]
  have h := morseReach_braid_cancel_swing r r (pairDeltaBar r) hD
    (morseOfBraid (pairRevTorusWord r s)) [] (by rw [morseOut_morseOfBraid_swing])
  rw [hc, List.append_assoc, morseOfBraid_append_swing]
  simpa only [List.append_nil] using h

end AJConjecture
