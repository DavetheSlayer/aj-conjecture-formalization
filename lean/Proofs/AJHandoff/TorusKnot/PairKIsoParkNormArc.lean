import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkNormDefs
import AJHandoff.TorusKnot.PairKIsoParkComm
import AJHandoff.TorusKnot.PairKIsoParkMacrosL
import AJHandoff.TorusKnot.PairKIsoBeadStep
import AJHandoff.TorusKnot.PairKIsoParkProc

/-!
# Stage C by ports, normalisation step 2: the beads of the left legs to the ports

The left leg of the arc `j` is the band `j < q`; it is traversed downwards, from its cap to its
cup. Its beads in `pairParkV1`, from bottom to top: the curl `p` of the left climb `isoBLC (j+1)`
(right after the doubled cup `u_j`); for `j = q - 1` the `E - 1` curls of the decreasing run and
the block `t n` of the last round (`isoBLast`, before the last doubled round); for `j < q - 1`
the block `t n` of the right descent `isoBRd (j + 1)` (right before the doubled cap `n_j`).

* The upper block slides down the leg (`morseReach_isoBead_commL`/`commR`: everything else on the
  word lies on other bands) onto the curls; the leg then carries `p^k · t n` (word frame,
  `k = E` or `1`), on the band `j` right after the doubled cup `u_j`.
* The stack turns around the cup (`morseReach_isoBead_cup`): on the right leg it reads
  `isoRot 2 (p^k · t n) = ln · t · lp^k` (`isoRot` of beads: `p ↦ lp`, `n ↦ ln`, `t ↦ t`), then
  `ln t → t ln` (`morseReach_isoPark_LNT`) and `ln lp → []` (`morseReach_isoPark_LNLP`, a
  `kink`): `t · lp^{k-1}`.
* It moves right past the inner doubled cups `u_{j+1} … u_{q-1}` (`commL`, two bands each) and
  past `u_{2q+1}` (`commR`): the port `q - 1 - j`. For `j = q - 1` the increasing run (on the
  band `q`) is already there, above it, and also passes `u_{2q+1}` (`commR`).
* The bottom block `t n` stays (bottom stack), the top curl stays (top stack).

The result is `pairParkV2` (the doubled cups and caps regrouped as `morseDouble (pairCups r)` and
`morseDouble (pairCaps r)`).
-/

namespace AJConjecture

/-- Rotation of a bead stack: `p ↦ lp`, `n ↦ ln`, `t ↦ t`, read backwards. -/
theorem isoRot_isoBeadsWord_curls (k : ℕ) :
    isoRot 2 (isoBeadsWord (List.replicate k .p ++ [.t, .n])) =
      isoBeadsWord ([.ln, .t] ++ List.replicate k .lp) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, show isoBeadsWord (IsoBead.p ::
      (List.replicate k IsoBead.p ++ [IsoBead.t, IsoBead.n])) = isoBeadsWord [.p] ++
      isoBeadsWord (List.replicate k IsoBead.p ++ [IsoBead.t, IsoBead.n]) by simp [isoBeadsWord],
      isoRot_append, show morseOut 2 (isoBeadsWord [.p]) = 2 by decide, ih,
      show isoRot 2 (isoBeadsWord [.p]) = isoBeadsWord [.lp] by decide, List.replicate_succ']
    simp [isoBeadsWord]


/-- The word of a concatenation of stacks. -/
private theorem isoBeadsWord_append_arc (L M : List IsoBead) :
    isoBeadsWord (L ++ M) = isoBeadsWord L ++ isoBeadsWord M :=
  List.flatMap_append

/-- A word fits on `N` strands, ends on `M` and acts only on the strands from `K` on. -/
private def ArcFits (N M K : ℕ) (w : MorseWord) : Prop :=
  morseFits N w = true ∧ morseOut N w = M ∧ ∀ l ∈ w, K ≤ l.2

/-- Arities of consecutive words compose. -/
private theorem ArcFits.append {N M L K : ℕ} {a b : MorseWord} (ha : ArcFits N M K a)
    (hb : ArcFits M L K b) : ArcFits N L K (a ++ b) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [morseFits_append, ha.1, ha.2.1, hb.1]; rfl
  · rw [morseOut_append, ha.2.1, hb.2.1]
  · intro l hl
    rcases List.mem_append.1 hl with h | h
    · exact ha.2.2 l h
    · exact hb.2.2 l h

/-- A weaker bound on the positions. -/
private theorem ArcFits.mono {N M K K' : ℕ} {w : MorseWord} (h : ArcFits N M K w) (hK : K' ≤ K) :
    ArcFits N M K' w :=
  ⟨h.1, h.2.1, fun l hl ↦ le_trans hK (h.2.2 l hl)⟩

/-- Changing the presentation of the arities. -/
private theorem ArcFits.of_eq {N M K N' M' : ℕ} {w : MorseWord} (h : ArcFits N M K w)
    (hN : N = N') (hM : M = M') : ArcFits N' M' K w := by
  subst hN hM
  exact h

/-- A run of equal blocks. -/
private theorem ArcFits.blk {N K : ℕ} {X : MorseWord} (h : ArcFits N N K X) (k : ℕ) :
    ArcFits N N K (phaseTwoBlk X k) := by
  induction k with
  | zero => exact ⟨rfl, rfl, by simp [phaseTwoBlk]⟩
  | succ k ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact h.append ih

/-- A shifted stack of beads. -/
private theorem arcFits_shift (d n : ℕ) (L : List IsoBead) (h : d + 2 ≤ n) :
    ArcFits n n d (morseShiftWord d (isoBeadsWord L)) := by
  have hL := morseFits_isoBeadsWord L 0
  have := morseOut_shift_iso d 2 (n - d - 2) (isoBeadsWord L) hL.1
  rw [hL.2, show d + 2 + (n - d - 2) = n by omega] at this
  refine ⟨this.2, this.1, ?_⟩
  intro l hl
  simp only [morseShiftWord, List.mem_map, shiftLetter] at hl
  obtain ⟨l', -, rfl⟩ := hl
  simp

/-- A doubled cup. -/
private theorem arcFits_cup (i n : ℕ) (h : 2 * i ≤ n) :
    ArcFits n (n + 4) (2 * i) (morseDouble [isoU i]) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [morseDouble, isoU, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      morseDoubleLetter, morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      and_true] <;> omega

/-- A doubled cap. -/
private theorem arcFits_cap (i n : ℕ) (h : 2 * i + 4 ≤ n) :
    ArcFits n (n - 4) (2 * i) (morseDouble [isoN i]) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [morseDouble, isoN, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      morseDoubleLetter, morseFits_cons, morseFits_nil, morseOut, morseLetterOut, morseKindIn,
      morseKindOut, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      and_true] <;> omega

/-- A doubled left walk. -/
private theorem arcFits_walk (p len n : ℕ) (h : 2 * (p + len) + 2 ≤ n) :
    ArcFits n n (2 * p) (morseDouble (morseWalkL true p len)) := by
  have hm : ∀ l ∈ morseDouble (morseWalkL true p len),
      (∃ s, l.1 = MorseKind.cross s) ∧ 2 * p ≤ l.2 ∧ l.2 ≤ 2 * (p + len) := by
    intro l hl
    simp only [morseDouble, List.mem_flatMap, morseWalkL, List.mem_map, List.mem_reverse,
      List.mem_range] at hl
    obtain ⟨_, ⟨i, hi, rfl⟩, hl⟩ := hl
    simp [morseDoubleLetter, cable, cableGen, morseOfBraid, List.range_succ] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> exact ⟨⟨_, rfl⟩, by simp only; omega⟩
  exact ⟨morseFits_of_cross _ _ (fun l hl ↦ (hm l hl).1)
    (fun l hl ↦ by have := (hm l hl).2.2; omega),
    morseOut_of_cross _ _ (fun l hl ↦ (hm l hl).1), fun l hl ↦ (hm l hl).2.1⟩

/-- The curl of a left climb above its doubled cup. -/
private def arcLC (i : ℕ) : MorseWord :=
  morseDouble [isoU i] ++ morseShiftWord (2 * i) (isoBeadsWord [.p])

/-- A left climb. -/
private theorem arcFits_LC (i n : ℕ) (h : 2 * i ≤ n) : ArcFits n (n + 4) (2 * i) (arcLC i) :=
  (arcFits_cup i n h).append (arcFits_shift _ _ _ (by omega))

/-- A run of left climbs. -/
private theorem arcFits_LCs (j n : ℕ) (h : 2 * j ≤ n) : ∀ m : ℕ,
    ArcFits n (n + 4 * m) (2 * j) ((List.range m).flatMap fun i ↦ arcLC (j + i))
  | 0 => ⟨rfl, rfl, by simp⟩
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact ((arcFits_LCs j n h m).append ((arcFits_LC (j + m) (n + 4 * m) (by omega)).mono
      (by omega))).of_eq rfl (by ring)

/-- A run of right descents (word order: from the inner leg outwards). -/
private def arcRdW (j m : ℕ) : MorseWord :=
  (List.range m).reverse.flatMap fun i ↦
    morseShiftWord (2 * (j + i)) (isoBeadsWord [.t, .n]) ++ morseDouble [isoN (j + i)]

/-- Arity of a run of right descents. -/
private theorem arcFits_RdW (j : ℕ) : ∀ (m n : ℕ), 2 * j + 4 * m ≤ n →
    ArcFits n (n - 4 * m) (2 * j) (arcRdW j m)
  | 0, n, _ => ⟨rfl, by simp [arcRdW, morseOut], by simp [arcRdW]⟩
  | m + 1, n, h => by
    have ih := arcFits_RdW j m (n - 4) (by omega)
    have h1 : ArcFits n (n - 4) (2 * j) (morseShiftWord (2 * (j + m)) (isoBeadsWord [.t, .n]) ++
        morseDouble [isoN (j + m)]) :=
      ((arcFits_shift _ _ _ (by omega)).append (arcFits_cap _ _ (by omega))).mono (by omega)
    rw [arcRdW, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.flatMap_cons, ← arcRdW]
    exact (h1.append ih).of_eq rfl (by omega)

/-- Shifted stacks placed one after the other. -/
private theorem arcFits_shifts (n K : ℕ) (f : ℕ → ℕ) (L : ℕ → List IsoBead) :
    ∀ cs : List ℕ, (∀ c ∈ cs, K ≤ f c ∧ f c + 2 ≤ n) →
      ArcFits n n K (cs.flatMap fun c ↦ morseShiftWord (f c) (isoBeadsWord (L c)))
  | [], _ => ⟨rfl, rfl, by simp⟩
  | c :: cs, h => by
    rw [List.flatMap_cons]
    exact ((arcFits_shift (f c) n (L c) (h c List.mem_cons_self).2).mono
      (h c List.mem_cons_self).1).append
      (arcFits_shifts n K f L cs fun c' hc' ↦ h c' (List.mem_cons_of_mem _ hc'))

/-- Doubled cups placed one after the other. -/
private theorem arcFits_cups (n : ℕ) : ∀ j : ℕ,
    ArcFits n (n + 4 * j) 0 ((List.range j).flatMap fun i ↦ morseDouble [isoU i])
  | 0 => ⟨rfl, rfl, by simp⟩
  | j + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact ((arcFits_cups n j).append ((arcFits_cup j (n + 4 * j) (by omega)).mono
      (Nat.zero_le _))).of_eq rfl (by ring)

/-- The decreasing and the increasing run. -/
private def arcDI (q E z : ℕ) : MorseWord :=
  morseShiftWord (2 * (q - 1)) (isoBeadsWord (List.replicate E .p)) ++
    morseShiftWord (2 * q) (isoBeadsWord (List.replicate z [IsoBead.t, .n]).flatten)

/-- The ports already reached by the legs `0, …, j - 1` (ports `q - j, …, q - 1`). -/
private def arcPorts (q j : ℕ) : MorseWord :=
  (List.range j).flatMap fun i ↦ morseShiftWord (2 * (q + (q - j + i))) (isoBeadsWord [.t])

/-- One doubled round. -/
private def arcDRound (q : ℕ) : MorseWord := morseDouble (morseWalkL true q (q + 1))

/-- The clasp stack, the first round and the middle rounds. -/
private def arcMid (q s : ℕ) : MorseWord :=
  morseShiftWord (2 * (2 * q + 1)) (isoBeadsWord [.t, .cs]) ++ arcDRound q ++
    phaseTwoBlk (arcDRound q ++ morseShiftWord (2 * q) (isoBeadsWord [.p])) (s - 2)

/-- The doubled caps of the legs `j - 1, …, 0`. -/
private def arcCaps (j : ℕ) : MorseWord :=
  (List.range j).reverse.flatMap fun i ↦ morseDouble [isoN i]

/-- The word after the legs `0, …, j - 1` are normalised. -/
private def arcState (q s E z j : ℕ) : MorseWord :=
  [isoU 1] ++ isoBeadsWord [.t, .n] ++ (List.range j).flatMap (fun i ↦ morseDouble [isoU i]) ++
    (List.range (q - j)).flatMap (fun i ↦ arcLC (j + i)) ++ arcDI q E z ++
    morseDouble [isoU (2 * q + 1)] ++ arcPorts q j ++ arcMid q s ++
    morseShiftWord (2 * (q - 1)) (isoBeadsWord [.t, .n]) ++ arcDRound q ++
    morseDouble [isoN (q - 1)] ++ morseDouble [isoN (2 * q - 1)] ++ arcRdW j (q - 1 - j) ++
    arcCaps j ++ isoBeadsWord [.p] ++ [isoN 1]

/-- The kink at the cup of a leg. -/
private theorem morseReach_arcKink (k : ℕ) :
    MorseReach 2 (isoBeadsWord ([.ln, .t] ++ List.replicate (k + 1) .lp))
      (isoBeadsWord ([.t] ++ List.replicate k .lp)) := by
  have h1 := morseReach_isoBeads_frame [] (List.replicate (k + 1) .lp) _ _ morseReach_isoPark_LNT
  have h2 := morseReach_isoBeads_frame [.t] (List.replicate k .lp) [.ln, .lp] []
    morseReach_isoPark_LNLP
  rw [List.replicate_succ] at h1
  simp only [List.nil_append, List.append_nil, List.cons_append] at h1 h2 ⊢
  exact morseReach_trans h1 h2

/-- The moves of one leg, for abstract words around it. -/
private theorem morseReach_arcLeg (H W U2 Rest V : MorseWord) (j M N : ℕ)
    (hH : morseOut 1 H = 4 * j + 3) (hW7 : ArcFits (4 * j + 7) N (2 * j + 2) W)
    (hW2 : morseFits (2 * j + 2) W = true ∧ morseOut (2 * j + 2) W = M)
    (hU2 : ArcFits N (N + 4) (M + 2) U2) (hM : 2 * j ≤ M) (hMN : M + 2 ≤ N)
    (hRest : morseFits (N + 4) Rest = true ∧ ∀ l ∈ Rest, 2 * j + 2 ≤ l.2) :
    MorseReach 1 (H ++ (morseDouble [isoU j] ++ morseShiftWord (2 * j) (isoBeadsWord [.p])) ++
        W ++ U2 ++ Rest ++ morseShiftWord (2 * j) (isoBeadsWord [.t, .n]) ++ V)
      (H ++ morseDouble [isoU j] ++ W ++ U2 ++ morseShiftWord M (isoBeadsWord [.t]) ++ Rest ++
        V) := by
  have hHU : morseOut 1 (H ++ morseDouble [isoU j]) = 4 * j + 7 := by
    rw [morseOut_append, hH, (arcFits_cup j (4 * j + 3) (by omega)).2.1]
  have hHUP : morseOut 1 (H ++ morseDouble [isoU j] ++
      morseShiftWord (2 * j) (isoBeadsWord [.p])) = 4 * j + 7 := by
    rw [morseOut_append, hHU, (arcFits_shift (2 * j) (4 * j + 7) [.p] (by omega)).2.1]
  have hR1f : morseFits (4 * j + 7) (W ++ U2 ++ Rest) = true := by
    rw [morseFits_append, morseFits_append, morseOut_append, hW7.1, hW7.2.1, hU2.1, hU2.2.1,
      hRest.1]; rfl
  have hR1p : ∀ l ∈ W ++ U2 ++ Rest, 2 * j + 2 ≤ l.2 := by
    intro l hl
    simp only [List.mem_append] at hl
    rcases hl with (h | h) | h
    · exact hW7.2.2 l h
    · have := hU2.2.2 l h; omega
    · exact hRest.2 l h
  have hTn : morseFits 2 (isoBeadsWord [.t, .n]) = true ∧
      morseOut 2 (isoBeadsWord [.t, .n]) = 2 := ⟨rfl, rfl⟩
  have hT : morseFits 2 (isoBeadsWord [.t]) = true ∧ morseOut 2 (isoBeadsWord [.t]) = 2 :=
    ⟨rfl, rfl⟩
  -- 1. the upper block slides down the leg onto the curl
  have s1 := morseReach_isoBead_commR 1 (2 * j) 2 (isoBeadsWord [.t, .n])
    (H ++ morseDouble [isoU j] ++ morseShiftWord (2 * j) (isoBeadsWord [.p])) (W ++ U2 ++ Rest) V
    hTn.1 hTn.2 hR1p (by rw [hHUP]; exact hR1f) (by rw [hHUP]; omega)
  -- 2. the stack turns around the cup of the leg
  have s2 := morseReach_isoBead_cup 1 j (isoBeadsWord [.p, .t, .n]) H (W ++ U2 ++ Rest ++ V)
    rfl rfl (by rw [hH]; omega)
  rw [show isoRot 2 (isoBeadsWord [.p, .t, .n]) = isoBeadsWord [.ln, .t, .lp] from
    isoRot_isoBeadsWord_curls 1] at s2
  -- 3. the kink
  have hk : MorseReach 2 (isoBeadsWord [.ln, .t, .lp]) (isoBeadsWord [.t]) := by
    simpa using morseReach_arcKink 0
  have s3 := morseReach_frame 2 1 (2 * j + 2) (2 * j + 3) (H ++ morseDouble [isoU j])
    (W ++ U2 ++ Rest ++ V) _ _ hk rfl (by rw [hHU]; omega)
  -- 4. the stack passes the inner climbs and the runs
  have s4 := morseReach_isoBead_commL 1 (2 * j + 2) 2 (2 * j + 3) (isoBeadsWord [.t])
    (H ++ morseDouble [isoU j]) W (U2 ++ Rest ++ V) hT.1 hT.2 hW2.1 (by rw [hHU]; omega)
  rw [hW2.2] at s4
  -- 5. and the doubled cup of the right arc
  have hHW : morseOut 1 (H ++ morseDouble [isoU j] ++ W) = N := by
    rw [morseOut_append, hHU, hW7.2.1]
  have s5 := morseReach_isoBead_commR 1 M 2 (isoBeadsWord [.t]) (H ++ morseDouble [isoU j] ++ W)
    U2 (Rest ++ V) hT.1 hT.2 hU2.2.2 (by rw [hHW]; exact hU2.1) (by rw [hHW]; omega)
  have eP : ∀ X : MorseWord, morseShiftWord (2 * j) (isoBeadsWord [.p]) ++
      (morseShiftWord (2 * j) (isoBeadsWord [.t, .n]) ++ X) =
      morseShiftWord (2 * j) (isoBeadsWord [.p, .t, .n]) ++ X := fun X ↦ by
    rw [← List.append_assoc, ← morseShiftWord_append]; rfl
  simp only [List.append_assoc] at s1 s2 s3 s4 s5 ⊢
  rw [eP] at s1
  exact morseReach_trans (morseReach_symm s1) <| morseReach_trans s2 <| morseReach_trans s3 <|
    morseReach_trans s4 s5

/-- One leg `j < q - 1`: its beads go to the port `q - 1 - j`. -/
private theorem morseReach_arcStep (q s E z j : ℕ) (hj : j + 2 ≤ q) :
    MorseReach 1 (arcState q s E z j) (arcState q s E z (j + 1)) := by
  have eLC : (List.range (q - j)).flatMap (fun i ↦ arcLC (j + i)) =
      arcLC j ++ (List.range (q - (j + 1))).flatMap (fun i ↦ arcLC (j + 1 + i)) := by
    rw [show q - j = q - (j + 1) + 1 by omega, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp only [Nat.succ_eq_add_one, Nat.add_zero]
    congr 2
    funext i
    congr 1
    omega
  have eRd : arcRdW j (q - 1 - j) = arcRdW (j + 1) (q - 1 - (j + 1)) ++
      (morseShiftWord (2 * j) (isoBeadsWord [.t, .n]) ++ morseDouble [isoN j]) := by
    rw [arcRdW, arcRdW, show q - 1 - j = q - 1 - (j + 1) + 1 by omega, List.range_succ_eq_map,
      List.reverse_cons, List.flatMap_append, ← List.map_reverse, List.flatMap_map]
    simp only [Nat.succ_eq_add_one, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Nat.add_zero, show ∀ a, j + 1 + a = j + (a + 1) from fun a ↦ by omega]
  have ePo : arcPorts q (j + 1) = morseShiftWord (2 * (q + (q - 1 - j))) (isoBeadsWord [.t]) ++
      arcPorts q j := by
    rw [arcPorts, arcPorts, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      show q - (j + 1) + 0 = q - 1 - j by omega]
    simp only [Nat.succ_eq_add_one,
      show ∀ a, q - (j + 1) + (a + 1) = q - j + a from fun a ↦ by omega]
  have eCa : arcCaps (j + 1) = morseDouble [isoN j] ++ arcCaps j := by
    simp [arcCaps, List.range_succ]
  have eHe : (List.range (j + 1)).flatMap (fun i ↦ morseDouble [isoU i]) =
      (List.range j).flatMap (fun i ↦ morseDouble [isoU i]) ++ morseDouble [isoU j] := by
    simp [List.range_succ]
  rw [arcState, arcState, eLC, eRd, ePo, eCa, eHe, arcLC]
  -- arities
  have hH : morseOut 1 ([isoU 1] ++ isoBeadsWord [.t, .n] ++
      (List.range j).flatMap (fun i ↦ morseDouble [isoU i])) = 4 * j + 3 := by
    rw [morseOut_append, morseOut_append, show morseOut 1 [isoU 1] = 3 from rfl,
      (morseFits_isoBeadsWord [.t, .n] 1).2, (arcFits_cups 3 j).2.1]
    ring
  have hHU : morseOut 1 ([isoU 1] ++ isoBeadsWord [.t, .n] ++
      (List.range j).flatMap (fun i ↦ morseDouble [isoU i]) ++ morseDouble [isoU j]) =
      4 * j + 7 := by
    rw [morseOut_append, hH, (arcFits_cup j (4 * j + 3) (by omega)).2.1]
  have hW := ((arcFits_LCs (j + 1) (4 * j + 7) (by omega) (q - (j + 1))).append
    (((arcFits_shift (2 * (q - 1)) (4 * j + 7 + 4 * (q - (j + 1))) (List.replicate E .p)
      (by omega)).mono (show 2 * (j + 1) ≤ 2 * (q - 1) by omega)).append
      ((arcFits_shift (2 * q) (4 * j + 7 + 4 * (q - (j + 1)))
        (List.replicate z [IsoBead.t, .n]).flatten (by omega)).mono (by omega))))
  rw [show 4 * j + 7 + 4 * (q - (j + 1)) = 4 * q + 3 by omega] at hW
  have hDR : ArcFits (4 * q + 7) (4 * q + 7) (2 * (j + 1)) (arcDRound q) :=
    (arcFits_walk q (q + 1) (4 * q + 7) (by omega)).mono (by omega)
  have hMid : ArcFits (4 * q + 7) (4 * q + 7) (2 * (j + 1)) (arcMid q s) :=
    ((arcFits_shift (2 * (2 * q + 1)) (4 * q + 7) [.t, .cs] (by omega)).mono (by omega)).append
      (hDR.append ((hDR.append ((arcFits_shift (2 * q) (4 * q + 7) [.p] (by omega)).mono
        (by omega))).blk (s - 2)))
  have hU2 : ArcFits (4 * q + 3) (4 * q + 7) (2 * (j + 1)) (morseDouble [isoU (2 * q + 1)]) :=
    (arcFits_cup (2 * q + 1) (4 * q + 3) (by omega)).mono (by omega)
  have hPo : ArcFits (4 * q + 7) (4 * q + 7) (2 * (j + 1)) (arcPorts q j) :=
    arcFits_shifts (4 * q + 7) (2 * (j + 1)) (fun i ↦ 2 * (q + (q - j + i))) (fun _ ↦ [.t])
      (List.range j) (fun c hc ↦ by have := List.mem_range.1 hc; constructor <;> omega)
  have hB : ArcFits (4 * q + 7) (4 * q + 7) (2 * (j + 1))
      (morseShiftWord (2 * (q - 1)) (isoBeadsWord [.t, .n])) :=
    (arcFits_shift (2 * (q - 1)) (4 * q + 7) [.t, .n] (by omega)).mono (by omega)
  have hN1 : ArcFits (4 * q + 7) (4 * q + 3) (2 * (j + 1)) (morseDouble [isoN (q - 1)]) :=
    ((arcFits_cap (q - 1) (4 * q + 7) (by omega)).mono (by omega)).of_eq rfl (by omega)
  have hN2 : ArcFits (4 * q + 3) (4 * q - 1) (2 * (j + 1)) (morseDouble [isoN (2 * q - 1)]) :=
    ((arcFits_cap (2 * q - 1) (4 * q + 3) (by omega)).mono (by omega)).of_eq rfl (by omega)
  have hRd : ArcFits (4 * q - 1) (4 * j + 7) (2 * (j + 1)) (arcRdW (j + 1) (q - 1 - (j + 1))) :=
    (arcFits_RdW (j + 1) (q - 1 - (j + 1)) (4 * q - 1) (by omega)).of_eq rfl (by omega)
  have hRest := (((((hPo.append hMid).append hB).append hDR).append hN1).append hN2).append hRd
  have hW2 := (arcFits_LCs (j + 1) (2 * j + 2) (by omega) (q - (j + 1))).append
    (((arcFits_shift (2 * (q - 1)) (2 * j + 2 + 4 * (q - (j + 1))) (List.replicate E .p)
      (by omega)).mono (show 2 * (j + 1) ≤ 2 * (q - 1) by omega)).append
      ((arcFits_shift (2 * q) (2 * j + 2 + 4 * (q - (j + 1)))
        (List.replicate z [IsoBead.t, .n]).flatten (by omega)).mono (by omega)))
  have h := morseReach_arcLeg _ _ (morseDouble [isoU (2 * q + 1)]) _
    (morseDouble [isoN j] ++ arcCaps j ++ isoBeadsWord [.p] ++ [isoN 1]) j
    (2 * (q + (q - 1 - j))) (4 * q + 3) hH (hW.mono (by omega))
    ⟨hW2.1, by rw [hW2.2.1]; omega⟩ ((arcFits_cup (2 * q + 1) (4 * q + 3) (by omega)).mono
      (by omega)) (by omega) (by omega) ⟨hRest.1, fun l hl ↦ by have := hRest.2.2 l hl; omega⟩
  rw [arcDI]
  simp only [List.append_assoc] at h ⊢
  exact h

/-- The word after all legs are normalised. -/
private def arcFinalW (q s E z : ℕ) : MorseWord :=
  [isoU 1] ++ isoBeadsWord [.t, .n] ++ (List.range q).flatMap (fun i ↦ morseDouble [isoU i]) ++
    morseDouble [isoU (2 * q + 1)] ++
    morseShiftWord (2 * q) (isoBeadsWord ([.t] ++ List.replicate E .lp ++
      (List.replicate z [IsoBead.t, .n]).flatten)) ++
    arcPorts q (q - 1) ++ arcMid q s ++ arcDRound q ++ morseDouble [isoN (q - 1)] ++
    morseDouble [isoN (2 * q - 1)] ++ arcCaps (q - 1) ++ isoBeadsWord [.p] ++ [isoN 1]

/-- The last leg `q - 1`: its beads and the increasing run go to the port `0`. -/
private theorem morseReach_arcFinal (q s E z : ℕ) (hq : 1 ≤ q) :
    MorseReach 1 (arcState q s E z (q - 1)) (arcFinalW q s E z) := by
  have eLC : (List.range (q - (q - 1))).flatMap (fun i ↦ arcLC (q - 1 + i)) = arcLC (q - 1) := by
    rw [show q - (q - 1) = 1 by omega]; simp
  have eRd : arcRdW (q - 1) (q - 1 - (q - 1)) = [] := by simp [arcRdW]
  have eHe : (List.range q).flatMap (fun i ↦ morseDouble [isoU i]) =
      (List.range (q - 1)).flatMap (fun i ↦ morseDouble [isoU i]) ++ morseDouble [isoU (q - 1)] := by
    conv_lhs => rw [show q = q - 1 + 1 by omega]
    simp [List.range_succ]
  rw [arcState, arcFinalW, eLC, eRd, eHe, arcLC, arcDI]
  have hH : morseOut 1 ([isoU 1] ++ isoBeadsWord [.t, .n] ++
      (List.range (q - 1)).flatMap (fun i ↦ morseDouble [isoU i])) = 4 * (q - 1) + 3 := by
    rw [morseOut_append, morseOut_append, show morseOut 1 [isoU 1] = 3 from rfl,
      (morseFits_isoBeadsWord [.t, .n] 1).2, (arcFits_cups 3 (q - 1)).2.1]
    ring
  have hHU : morseOut 1 ([isoU 1] ++ isoBeadsWord [.t, .n] ++
      (List.range (q - 1)).flatMap (fun i ↦ morseDouble [isoU i]) ++ morseDouble [isoU (q - 1)]) =
      4 * q + 3 := by
    rw [morseOut_append, hH, (arcFits_cup (q - 1) (4 * (q - 1) + 3) (by omega)).2.1]; omega
  have hHUPD : morseOut 1 ([isoU 1] ++ isoBeadsWord [.t, .n] ++
      (List.range (q - 1)).flatMap (fun i ↦ morseDouble [isoU i]) ++
      (morseDouble [isoU (q - 1)] ++ morseShiftWord (2 * (q - 1)) (isoBeadsWord [.p])) ++
      morseShiftWord (2 * (q - 1)) (isoBeadsWord (List.replicate E .p))) = 4 * q + 3 := by
    rw [← List.append_assoc, morseOut_append, morseOut_append, hHU,
      (arcFits_shift (2 * (q - 1)) (4 * q + 3) [.p] (by omega)).2.1,
      (arcFits_shift (2 * (q - 1)) (4 * q + 3) (List.replicate E .p) (by omega)).2.1]
  have hR : ArcFits (4 * q + 3) (4 * q + 7) (2 * q)
      (morseShiftWord (2 * q) (isoBeadsWord (List.replicate z [IsoBead.t, .n]).flatten) ++
        morseDouble [isoU (2 * q + 1)] ++ arcPorts q (q - 1) ++ arcMid q s) := by
    have hDR : ArcFits (4 * q + 7) (4 * q + 7) (2 * q) (arcDRound q) :=
      arcFits_walk q (q + 1) (4 * q + 7) (by omega)
    refine (((arcFits_shift (2 * q) (4 * q + 3) _ (by omega)).append
      ((arcFits_cup (2 * q + 1) (4 * q + 3) (by omega)).mono (by omega))).append
      (arcFits_shifts (4 * q + 7) (2 * q) (fun i ↦ 2 * (q + (q - (q - 1) + i))) (fun _ ↦ [.t])
        (List.range (q - 1)) (fun c hc ↦ by have := List.mem_range.1 hc; constructor <;> omega))).append
      (((arcFits_shift (2 * (2 * q + 1)) (4 * q + 7) [.t, .cs] (by omega)).mono (by omega)).append
        (hDR.append ((hDR.append ((arcFits_shift (2 * q) (4 * q + 7) [.p] (by omega)))).blk
          (s - 2))))
  have hTn : morseFits 2 (isoBeadsWord [.t, .n]) = true ∧
      morseOut 2 (isoBeadsWord [.t, .n]) = 2 := ⟨rfl, rfl⟩
  -- 1. the block of the last round slides down the leg onto the curls
  have f1 := morseReach_isoBead_commR 1 (2 * (q - 1)) 2 (isoBeadsWord [.t, .n])
    ([isoU 1] ++ isoBeadsWord [.t, .n] ++
      (List.range (q - 1)).flatMap (fun i ↦ morseDouble [isoU i]) ++
      (morseDouble [isoU (q - 1)] ++ morseShiftWord (2 * (q - 1)) (isoBeadsWord [.p])) ++
      morseShiftWord (2 * (q - 1)) (isoBeadsWord (List.replicate E .p)))
    (morseShiftWord (2 * q) (isoBeadsWord (List.replicate z [IsoBead.t, .n]).flatten) ++
        morseDouble [isoU (2 * q + 1)] ++ arcPorts q (q - 1) ++ arcMid q s)
    (arcDRound q ++ morseDouble [isoN (q - 1)] ++ morseDouble [isoN (2 * q - 1)] ++ [] ++
      arcCaps (q - 1) ++ isoBeadsWord [.p] ++ [isoN 1]) hTn.1 hTn.2
    (fun l hl ↦ by have := hR.2.2 l hl; omega) (by rw [hHUPD]; exact hR.1)
    (by rw [hHUPD]; omega)
  -- 2. the stack turns around the cup
  have hS := morseFits_isoBeadsWord (List.replicate (E + 1) .p ++ [.t, .n]) 0
  have f2 := morseReach_isoBead_cup 1 (q - 1) (isoBeadsWord (List.replicate (E + 1) .p ++ [.t, .n]))
    ([isoU 1] ++ isoBeadsWord [.t, .n] ++
      (List.range (q - 1)).flatMap (fun i ↦ morseDouble [isoU i]))
    (morseShiftWord (2 * q) (isoBeadsWord (List.replicate z [IsoBead.t, .n]).flatten) ++
        morseDouble [isoU (2 * q + 1)] ++ arcPorts q (q - 1) ++ arcMid q s ++
      (arcDRound q ++ morseDouble [isoN (q - 1)] ++ morseDouble [isoN (2 * q - 1)] ++ [] ++
      arcCaps (q - 1) ++ isoBeadsWord [.p] ++ [isoN 1])) hS.1 hS.2 (by rw [hH]; omega)
  rw [isoRot_isoBeadsWord_curls, show 2 * (q - 1) + 2 = 2 * q by omega] at f2
  -- 3. the kink
  have f3 := morseReach_frame 2 1 (2 * q) (2 * q + 1)
    ([isoU 1] ++ isoBeadsWord [.t, .n] ++
      (List.range (q - 1)).flatMap (fun i ↦ morseDouble [isoU i]) ++ morseDouble [isoU (q - 1)])
    (morseShiftWord (2 * q) (isoBeadsWord (List.replicate z [IsoBead.t, .n]).flatten) ++
        morseDouble [isoU (2 * q + 1)] ++ arcPorts q (q - 1) ++ arcMid q s ++
      (arcDRound q ++ morseDouble [isoN (q - 1)] ++ morseDouble [isoN (2 * q - 1)] ++ [] ++
      arcCaps (q - 1) ++ isoBeadsWord [.p] ++ [isoN 1])) _ _ (morseReach_arcKink E)
    (morseFits_isoBeadsWord _ 0).1 (by rw [hHU]; omega)
  -- 4. with the increasing run it passes the doubled cup of the right arc
  have hS0 := morseFits_isoBeadsWord ([.t] ++ List.replicate E .lp ++
      (List.replicate z [IsoBead.t, .n]).flatten) 0
  have f4 := morseReach_isoBead_commR 1 (2 * q) 2 (isoBeadsWord ([.t] ++ List.replicate E .lp ++
      (List.replicate z [IsoBead.t, .n]).flatten))
    ([isoU 1] ++ isoBeadsWord [.t, .n] ++
      (List.range (q - 1)).flatMap (fun i ↦ morseDouble [isoU i]) ++ morseDouble [isoU (q - 1)])
    (morseDouble [isoU (2 * q + 1)])
    (arcPorts q (q - 1) ++ arcMid q s ++
      (arcDRound q ++ morseDouble [isoN (q - 1)] ++ morseDouble [isoN (2 * q - 1)] ++ [] ++
      arcCaps (q - 1) ++ isoBeadsWord [.p] ++ [isoN 1])) hS0.1 hS0.2
    (fun l hl ↦ by have := (arcFits_cup (2 * q + 1) (4 * q + 3) (by omega)).2.2 l hl; omega)
    (by rw [hHU]; exact (arcFits_cup (2 * q + 1) (4 * q + 3) (by omega)).1) (by rw [hHU]; omega)
  have e1 : ∀ X : MorseWord, morseShiftWord (2 * (q - 1)) (isoBeadsWord [.p]) ++
      (morseShiftWord (2 * (q - 1)) (isoBeadsWord (List.replicate E .p)) ++
        (morseShiftWord (2 * (q - 1)) (isoBeadsWord [.t, .n]) ++ X)) =
      morseShiftWord (2 * (q - 1)) (isoBeadsWord (List.replicate (E + 1) .p ++ [.t, .n])) ++ X := by
    intro X
    rw [← List.append_assoc, ← List.append_assoc, ← morseShiftWord_append, ← morseShiftWord_append]
    congr 2
    simp [isoBeadsWord, List.replicate_succ]
  have e2 : ∀ X : MorseWord, morseShiftWord (2 * q) (isoBeadsWord ([.t] ++ List.replicate E .lp)) ++
      (morseShiftWord (2 * q) (isoBeadsWord (List.replicate z [IsoBead.t, .n]).flatten) ++ X) =
      morseShiftWord (2 * q) (isoBeadsWord ([.t] ++ List.replicate E .lp ++
        (List.replicate z [IsoBead.t, .n]).flatten)) ++ X := by
    intro X
    rw [← List.append_assoc, ← morseShiftWord_append, ← isoBeadsWord_append_arc]
  simp only [List.append_assoc, List.nil_append] at f1 f2 f3 f4 ⊢
  rw [e1] at f1
  rw [e2] at f3
  exact morseReach_trans (morseReach_symm f1) <| morseReach_trans f2 <| morseReach_trans f3 f4

/-- A run of equal shifted stacks is one shifted stack. -/
private theorem phaseTwoBlk_shift_arc (d : ℕ) (L : List IsoBead) : ∀ k : ℕ,
    phaseTwoBlk (morseShiftWord d (isoBeadsWord L)) k =
      morseShiftWord d (isoBeadsWord (List.replicate k L).flatten)
  | 0 => rfl
  | k + 1 => by
    rw [phaseTwoBlk, List.replicate_succ, List.flatten_cons, ← phaseTwoBlk,
      phaseTwoBlk_shift_arc d L k, List.replicate_succ, List.flatten_cons, isoBeadsWord_append_arc,
      morseShiftWord_append]

/-- `pairParkV1` is the word before the first leg. -/
private theorem pairParkV1_eq_arc (q s : ℕ) (hq : 1 ≤ q) :
    pairParkV1 (q + 2) s =
      arcState q s (pairRunDown (q + 2) s - 1) (pairRunUp (q + 2) s + 1) 0 := by
  have hLC : ∀ i, isoBLC (i + 1) = arcLC i := by
    intro i
    simp only [isoBLC, arcLC, Nat.add_sub_cancel, morseDouble, isoU, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, morseDoubleLetter, morseShiftWord_append]
    simp [morseShiftWord, shiftLetter, isoBeadsWord, isoBeadWord]
    omega
  have hLCs : (List.range (q + 2 - 2 - 1)).flatMap (fun i ↦ isoBLC (i + 1)) ++ isoBLC (q + 2 - 2) =
      (List.range (q - 0)).flatMap (fun i ↦ arcLC (0 + i)) := by
    rw [show q + 2 - 2 - 1 = q - 1 by omega, show q + 2 - 2 = q - 1 + 1 by omega, hLC,
      show q - 0 = q - 1 + 1 by omega, List.range_succ, List.flatMap_append]
    simp [hLC]
  have hDec : phaseTwoBlk (isoBDec (q + 2 - 2)) (pairRunDown (q + 2) s - 1) =
      morseShiftWord (2 * (q - 1)) (isoBeadsWord (List.replicate (pairRunDown (q + 2) s - 1) .p)) := by
    rw [show isoBDec (q + 2 - 2) = morseShiftWord (2 * (q - 1)) (isoBeadsWord [.p]) by
      simp [isoBDec, isoBeadsWord, isoBeadWord], phaseTwoBlk_shift_arc]
    congr 2
    simp
  have hInc : phaseTwoBlk (isoBInc (q + 2 - 2)) (pairRunUp (q + 2) s + 1) =
      morseShiftWord (2 * q) (isoBeadsWord (List.replicate (pairRunUp (q + 2) s + 1)
        [IsoBead.t, .n]).flatten) := by
    rw [show isoBInc (q + 2 - 2) = morseShiftWord (2 * q) (isoBeadsWord [.t, .n]) by
      simp only [isoBInc, Nat.add_sub_cancel]; rfl, phaseTwoBlk_shift_arc]
  have hDR : pairDRound (q + 2) = arcDRound q := by
    simp only [pairDRound, arcDRound, Nat.add_sub_cancel, show q + 2 - 1 = q + 1 by omega]
  have hRound : isoBRound (q + 2 - 2) (q + 2) =
      arcDRound q ++ morseShiftWord (2 * q) (isoBeadsWord [.p]) := by
    simp only [isoBRound, arcDRound, Nat.add_sub_cancel, show q + 2 - 1 = q + 1 by omega]
    simp [isoBeadsWord, isoBeadWord]
  have hLast : isoBLast (q + 2 - 2) (q + 2) = morseShiftWord (2 * (q - 1))
      (isoBeadsWord [.t, .n]) ++ arcDRound q ++ morseDouble [isoN (q - 1)] := by
    simp only [isoBLast, arcDRound, Nat.add_sub_cancel, show q + 2 - 1 = q + 1 by omega,
      morseDouble, List.flatMap_append, List.append_assoc]
    rfl
  have hRd : pairPlumbRd (q + 2) = arcRdW 0 (q - 1 - 0) := by
    simp only [pairPlumbRd, arcRdW, isoBRd, Nat.add_sub_cancel, Nat.zero_add, Nat.sub_zero]
    rfl
  rw [pairParkV1, pairPlumbPre, arcState, show 2 * (q + 2) - 3 = 2 * q + 1 by omega,
    show 2 * (q + 2) - 5 = 2 * q - 1 by omega, hDR, hRound, hLast, hRd, hDec, hInc,
    List.append_assoc ([isoU 1] ++ phaseTwoA1), hLCs]
  simp only [arcDI, arcMid, arcPorts, arcCaps, List.range_zero, List.flatMap_nil, List.reverse_nil,
    List.append_nil, List.append_assoc]
  rfl

/-- `pairParkV2` is the word after the last leg. -/
private theorem pairParkV2_eq_arc (q s : ℕ) (hq : 1 ≤ q) :
    pairParkV2 (q + 2) s =
      arcFinalW q s (pairRunDown (q + 2) s - 1) (pairRunUp (q + 2) s + 1) := by
  have hDR : pairDRound (q + 2) = arcDRound q := by
    simp only [pairDRound, arcDRound, Nat.add_sub_cancel, show q + 2 - 1 = q + 1 by omega]
  have hcups : morseDouble (pairCups (q + 2)) =
      (List.range q).flatMap (fun i ↦ morseDouble [isoU i]) ++ morseDouble [isoU (2 * q + 1)] := by
    simp only [pairCups, morseDouble, List.flatMap_append, List.flatMap_map, Nat.add_sub_cancel,
      show 2 * (q + 2) - 3 = 2 * q + 1 by omega]
    rfl
  have hcaps : morseDouble (pairCaps (q + 2)) =
      morseDouble [isoN (q - 1)] ++ morseDouble [isoN (2 * q - 1)] ++ arcCaps (q - 1) := by
    simp only [pairCaps, arcCaps, morseDouble, List.flatMap_append, List.flatMap_map,
      show q + 2 - 3 = q - 1 by omega, show 2 * (q + 2) - 5 = 2 * q - 1 by omega,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hports : (List.range (q + 2)).flatMap (fun c ↦ morseShiftWord (2 * (q + 2 - 2 + c))
      (isoBeadsWord (pairParkS2 (q + 2) s c))) =
      morseShiftWord (2 * q) (isoBeadsWord ([.t] ++ List.replicate (pairRunDown (q + 2) s - 1) .lp ++
        (List.replicate (pairRunUp (q + 2) s + 1) [IsoBead.t, .n]).flatten)) ++
      arcPorts q (q - 1) ++ morseShiftWord (2 * (2 * q + 1)) (isoBeadsWord [.t, .cs]) := by
    rw [show q + 2 = q - 1 + 1 + 1 + 1 by omega, List.range_succ, List.range_succ,
      List.range_succ_eq_map]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_map, List.flatMap_nil,
      List.append_nil, arcPorts, Nat.succ_eq_add_one]
    have e0 : pairParkS2 (q - 1 + 1 + 1 + 1) s 0 = [.t] ++
        List.replicate (pairRunDown (q - 1 + 1 + 1 + 1) s - 1) .lp ++
        (List.replicate (pairRunUp (q - 1 + 1 + 1 + 1) s + 1) [IsoBead.t, .n]).flatten := by
      simp [pairParkS2]
    have emid : ∀ i ∈ List.range (q - 1), pairParkS2 (q - 1 + 1 + 1 + 1) s (i + 1) = [.t] := by
      intro i hi
      have := List.mem_range.1 hi
      rw [pairParkS2]; split_ifs <;> first | omega | contradiction | rfl
    have eq : pairParkS2 (q - 1 + 1 + 1 + 1) s (q - 1 + 1) = [] := by
      rw [pairParkS2]; split_ifs <;> first | omega | contradiction | rfl
    have el : pairParkS2 (q - 1 + 1 + 1 + 1) s (q - 1 + 1 + 1) = [.t, .cs] := by
      rw [pairParkS2]; split_ifs <;> first | omega | contradiction | rfl
    rw [e0, eq, el, List.flatMap_congr (fun i hi ↦ by rw [emid i hi])]
    simp only [show q - 1 + 1 = q by omega,
      show q - (q - 1) = 1 by omega, isoBeadsWord, List.flatMap_nil, morseShiftWord,
      List.map_nil, List.append_nil, List.append_assoc]
    congr 2
    · apply List.flatMap_congr
      intro i _
      congr 3
      omega
    · congr 3
      omega
  rw [pairParkV2, pairParkWX, arcFinalW, hcups, hports, hcaps, hDR]
  simp only [arcMid, Nat.add_sub_cancel, List.append_assoc]

/-- Normalisation step 2. -/
theorem morseReach_pairParkV1_V2 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairParkV1 r s) (pairParkV2 r s) := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 2 := ⟨r - 2, by omega⟩
  have hq : 1 ≤ q := by omega
  rw [pairParkV1_eq_arc q s hq, pairParkV2_eq_arc q s hq]
  have key : ∀ j, j + 1 ≤ q → MorseReach 1
      (arcState q s (pairRunDown (q + 2) s - 1) (pairRunUp (q + 2) s + 1) 0)
      (arcState q s (pairRunDown (q + 2) s - 1) (pairRunUp (q + 2) s + 1) j) := by
    intro j
    induction j with
    | zero => intro _; exact morseReach_refl 1 _
    | succ j ih =>
      intro hj
      exact morseReach_trans (ih (by omega)) (morseReach_arcStep _ _ _ _ j (by omega))
  exact morseReach_trans (key (q - 1) (by omega)) (morseReach_arcFinal _ _ _ _ hq)


end AJConjecture
