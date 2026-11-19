import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkWords
import AJHandoff.TorusKnot.PairKIsoParkMacros
import AJHandoff.TorusKnot.PairKIsoParkMacrosL
import AJHandoff.TorusKnot.PairKIsoParkCross

/-!
# Stage C by ports: processing a stack at the clasp (generic in the stack)

On two strands, a stack `Lb · cs · La` of beads `t, p, n, lp` (one clasp) is brought to
the normal form `T^t · cS(w_b) · cs · cS(w_a)` (`isoCurlStack`): all twists before the clasp,
one signed curl stack on each side of it.

* `morseReach_isoProc_after`: the beads after the clasp are processed from the clasp outwards:
  `p`/`n` join the curl stack (`PN`, `NP` cancel opposite curls); `lp` passes the curl stack
  (`LPP`, `LPN`) and crosses to the right edge at the clasp (`CSLP`); `t` passes the curl stack
  (`TP`, `NT`) and crosses the clasp (`K6`, `morseReach_isoPark_cross`), leaving `n n` before and
  `p p` after it; the `t n n` before the clasp is sorted into the twist run and the curl stack
  there.
* `morseReach_isoProc_before`: the beads before the clasp are processed from the clasp
  backwards: `t` joins the twist run; `p`/`n` pass it (`TP`, `NT`) and join the curl stack;
  `lp` passes the twists (`LPT`) and the curl stack (`LPP`, `LPN`) and crosses at the clasp
  (`LPCS`).
* `morseReach_isoProc`: both together.

Induction on the lists; every step is one fixed macro framed by `morseReach_frame` on two
strands.
-/

namespace AJConjecture

/-- The beads allowed in a processed stack. -/
def IsoProcBead (x : IsoBead) : Prop := x = .t ∨ x = .p ∨ x = .n ∨ x = .lp

/-- A move between bead stacks can be done inside a longer stack. -/
private theorem morseReach_procBeads_frame (U V A B : List IsoBead)
    (h : MorseReach 2 (isoBeadsWord A) (isoBeadsWord B)) :
    MorseReach 2 (isoBeadsWord (U ++ A ++ V)) (isoBeadsWord (U ++ B ++ V)) := by
  have hf := morseReach_frame 2 2 0 0 (isoBeadsWord U) (isoBeadsWord V) _ _ h
    (morseFits_isoBeadsWord A 0).1 (by rw [(morseFits_isoBeadsWord U 0).2])
  simpa only [isoBeadsWord, List.flatMap_append, morseShiftWord_zero_iso] using hf

/-- A bead commuting with `b` commutes with a run of it. -/
private theorem morseReach_procBeads_commRep (a b : IsoBead)
    (hc : MorseReach 2 (isoBeadsWord [a, b]) (isoBeadsWord [b, a])) :
    ∀ k : ℕ, MorseReach 2 (isoBeadsWord (List.replicate k a ++ [b]))
      (isoBeadsWord ([b] ++ List.replicate k a))
  | 0 => morseReach_refl 2 _
  | k + 1 => by
    have h1 := morseReach_procBeads_frame (List.replicate k a) [] [a, b] [b, a] hc
    have h2 := morseReach_procBeads_frame [] [a] _ _ (morseReach_procBeads_commRep a b hc k)
    rw [List.replicate_succ', List.append_assoc]
    simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- The curl stack of a natural number. -/
private theorem isoCurlStack_ofNat_proc (k : ℕ) :
    isoCurlStack (k : ℤ) = List.replicate k .p := by
  simp [isoCurlStack]

/-- The curl stack of a negative number. -/
private theorem isoCurlStack_neg_proc (k : ℕ) :
    isoCurlStack (-(k : ℤ)) = List.replicate k .n := by
  rcases k with _ | k
  · simp [isoCurlStack]
  · have h0 : ¬ (0 ≤ -((k + 1 : ℕ) : ℤ)) := by omega
    simp only [isoCurlStack, h0, ↓reduceIte, neg_neg, Int.toNat_natCast]

/-- A bead commuting with `p` and `n` commutes with every curl stack. -/
private theorem morseReach_procBeads_commStack (b : IsoBead)
    (hp : MorseReach 2 (isoBeadsWord [.p, b]) (isoBeadsWord [b, .p]))
    (hn : MorseReach 2 (isoBeadsWord [.n, b]) (isoBeadsWord [b, .n])) (w : ℤ) :
    MorseReach 2 (isoBeadsWord (isoCurlStack w ++ [b])) (isoBeadsWord ([b] ++ isoCurlStack w)) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg w
  · rw [isoCurlStack_ofNat_proc]; exact morseReach_procBeads_commRep _ _ hp k
  · rw [isoCurlStack_neg_proc]; exact morseReach_procBeads_commRep _ _ hn k

/-- A curl `p` joins a curl stack from the right. -/
private theorem morseReach_procBeads_stackP (w : ℤ) :
    MorseReach 2 (isoBeadsWord (isoCurlStack w ++ [.p])) (isoBeadsWord (isoCurlStack (w + 1))) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg w
  · rw [isoCurlStack_ofNat_proc, show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      isoCurlStack_ofNat_proc, List.replicate_succ']
    exact morseReach_refl 2 _
  · rcases k with _ | k
    · rw [show -((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) by simp, isoCurlStack_ofNat_proc,
        show ((0 : ℕ) : ℤ) + 1 = ((1 : ℕ) : ℤ) by simp, isoCurlStack_ofNat_proc]
      exact morseReach_refl 2 _
    · rw [isoCurlStack_neg_proc, show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) by push_cast; ring,
        isoCurlStack_neg_proc, List.replicate_succ', List.append_assoc]
      have h := morseReach_procBeads_frame (List.replicate k .n) [] [.n, .p] [] morseReach_isoPark_NP
      simpa only [List.append_nil, List.singleton_append] using h

/-- A curl `n` joins a curl stack from the right. -/
private theorem morseReach_procBeads_stackN (w : ℤ) :
    MorseReach 2 (isoBeadsWord (isoCurlStack w ++ [.n])) (isoBeadsWord (isoCurlStack (w - 1))) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg w
  · rcases k with _ | k
    · rw [show ((0 : ℕ) : ℤ) = -((0 : ℕ) : ℤ) by simp, isoCurlStack_neg_proc,
        show -((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) by simp, isoCurlStack_neg_proc]
      exact morseReach_refl 2 _
    · rw [isoCurlStack_ofNat_proc, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring,
        isoCurlStack_ofNat_proc, List.replicate_succ', List.append_assoc]
      have h := morseReach_procBeads_frame (List.replicate k .p) [] [.p, .n] [] morseReach_isoPark_PN
      simpa only [List.append_nil, List.singleton_append] using h
  · rw [isoCurlStack_neg_proc, show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring,
      isoCurlStack_neg_proc, List.replicate_succ']
    exact morseReach_refl 2 _

/-- A curl `p` joins a curl stack from the left. -/
private theorem morseReach_procBeads_pStack (w : ℤ) :
    MorseReach 2 (isoBeadsWord ([.p] ++ isoCurlStack w)) (isoBeadsWord (isoCurlStack (w + 1))) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg w
  · rw [isoCurlStack_ofNat_proc, show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      isoCurlStack_ofNat_proc, List.replicate_succ]
    exact morseReach_refl 2 _
  · rcases k with _ | k
    · rw [show -((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) by simp, isoCurlStack_ofNat_proc,
        show ((0 : ℕ) : ℤ) + 1 = ((1 : ℕ) : ℤ) by simp, isoCurlStack_ofNat_proc]
      exact morseReach_refl 2 _
    · rw [isoCurlStack_neg_proc, show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) by push_cast; ring,
        isoCurlStack_neg_proc, List.replicate_succ]
      have h := morseReach_procBeads_frame [] (List.replicate k .n) [.p, .n] [] morseReach_isoPark_PN
      simpa only [List.append_nil, List.nil_append, List.singleton_append, List.cons_append]
        using h

/-- A curl `n` joins a curl stack from the left. -/
private theorem morseReach_procBeads_nStack (w : ℤ) :
    MorseReach 2 (isoBeadsWord ([.n] ++ isoCurlStack w)) (isoBeadsWord (isoCurlStack (w - 1))) := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg w
  · rcases k with _ | k
    · rw [show ((0 : ℕ) : ℤ) = -((0 : ℕ) : ℤ) by simp, isoCurlStack_neg_proc,
        show -((0 : ℕ) : ℤ) - 1 = -((1 : ℕ) : ℤ) by simp, isoCurlStack_neg_proc]
      exact morseReach_refl 2 _
    · rw [isoCurlStack_ofNat_proc, show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by push_cast; ring,
        isoCurlStack_ofNat_proc, List.replicate_succ]
      have h := morseReach_procBeads_frame [] (List.replicate k .p) [.n, .p] [] morseReach_isoPark_NP
      simpa only [List.append_nil, List.nil_append, List.singleton_append, List.cons_append]
        using h
  · rw [isoCurlStack_neg_proc, show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring,
      isoCurlStack_neg_proc, List.replicate_succ]
    exact morseReach_refl 2 _

/-- The empty curl stack. -/
private theorem isoCurlStack_zero_proc : isoCurlStack 0 = [] := by
  simp [isoCurlStack]

/-- Processing the beads after the clasp. -/
theorem morseReach_isoProc_after (La : List IsoBead) (hLa : ∀ x ∈ La, IsoProcBead x)
    (t₀ : ℕ) (w₀ w₁ : ℤ) :
    MorseReach 2
      (isoBeadsWord (List.replicate t₀ .t ++ isoCurlStack w₀ ++ [.cs] ++ isoCurlStack w₁ ++ La))
      (isoBeadsWord (List.replicate (t₀ + isoBeadCountT La) .t ++
        isoCurlStack (w₀ - 2 * isoBeadCountT La) ++ [.cs] ++
        isoCurlStack (w₁ + isoBeadWr La + 2 * isoBeadCountT La))) := by
  induction La generalizing t₀ w₀ w₁ with
  | nil => simpa [isoBeadCountT, isoBeadWr] using morseReach_refl 2 _
  | cons x La ih =>
    have hLa' : ∀ y ∈ La, IsoProcBead y := fun y hy ↦ hLa y (List.mem_cons_of_mem _ hy)
    rcases hLa x List.mem_cons_self with rfl | rfl | rfl | rfl
    · have s1 := morseReach_procBeads_frame (List.replicate t₀ .t ++ isoCurlStack w₀ ++ [.cs]) La
        _ _ (morseReach_procBeads_commStack .t (morseReach_symm morseReach_isoPark_TP)
          morseReach_isoPark_NT w₁)
      have s2 := morseReach_procBeads_frame (List.replicate t₀ .t ++ isoCurlStack w₀)
        (isoCurlStack w₁ ++ La) _ _ morseReach_isoPark_cross
      have s3 := morseReach_procBeads_frame (List.replicate t₀ .t)
        ([.n, .n, .cs, .p, .p] ++ isoCurlStack w₁ ++ La) _ _
        (morseReach_procBeads_commStack .t (morseReach_symm morseReach_isoPark_TP)
          morseReach_isoPark_NT w₀)
      have s4 := morseReach_procBeads_frame (List.replicate t₀ .t ++ [.t])
        ([.n, .cs, .p, .p] ++ isoCurlStack w₁ ++ La) _ _ (morseReach_procBeads_stackN w₀)
      have s5 := morseReach_procBeads_frame (List.replicate t₀ .t ++ [.t])
        ([.cs, .p, .p] ++ isoCurlStack w₁ ++ La) _ _ (morseReach_procBeads_stackN (w₀ - 1))
      have s6 := morseReach_procBeads_frame
        (List.replicate t₀ .t ++ [.t] ++ isoCurlStack (w₀ - 1 - 1) ++ [.cs, .p]) La _ _
        (morseReach_procBeads_pStack w₁)
      have s7 := morseReach_procBeads_frame
        (List.replicate t₀ .t ++ [.t] ++ isoCurlStack (w₀ - 1 - 1) ++ [.cs]) La _ _
        (morseReach_procBeads_pStack (w₁ + 1))
      have s8 := ih hLa' (t₀ + 1) (w₀ - 1 - 1) (w₁ + 1 + 1)
      rw [List.replicate_succ'] at s8
      have e1 : t₀ + isoBeadCountT (.t :: La) = t₀ + 1 + isoBeadCountT La := by
        simp only [isoBeadCountT, List.count_cons_self]; ring
      have e2 : w₀ - 2 * ((isoBeadCountT (.t :: La) : ℕ) : ℤ) =
          w₀ - 1 - 1 - 2 * ((isoBeadCountT La : ℕ) : ℤ) := by
        simp only [isoBeadCountT, List.count_cons_self]; push_cast; ring
      have e3 : w₁ + isoBeadWr (.t :: La) + 2 * ((isoBeadCountT (.t :: La) : ℕ) : ℤ) =
          w₁ + 1 + 1 + isoBeadWr La + 2 * ((isoBeadCountT La : ℕ) : ℤ) := by
        simp only [isoBeadCountT, isoBeadWr, List.count_cons_self, List.count_cons]
        simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte]; push_cast; ring
      rw [e1, e2, e3]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
        at s1 s2 s3 s4 s5 s6 s7 s8 ⊢
      exact morseReach_trans s1 <| morseReach_trans s2 <| morseReach_trans s3 <|
        morseReach_trans s4 <| morseReach_trans s5 <| morseReach_trans s6 <| morseReach_trans s7 s8
    · have s1 := morseReach_procBeads_frame (List.replicate t₀ .t ++ isoCurlStack w₀ ++ [.cs]) La
        _ _ (morseReach_procBeads_stackP w₁)
      have s2 := ih hLa' t₀ w₀ (w₁ + 1)
      have e3 : w₁ + isoBeadWr (.p :: La) + 2 * ((isoBeadCountT La : ℕ) : ℤ) =
          w₁ + 1 + isoBeadWr La + 2 * ((isoBeadCountT La : ℕ) : ℤ) := by
        simp only [isoBeadCountT, isoBeadWr, List.count_cons]
        simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte]; push_cast; ring
      have e1 : isoBeadCountT (.p :: La) = isoBeadCountT La := by simp [isoBeadCountT]
      rw [e1, e3]
      simp only [List.append_assoc, List.cons_append, List.nil_append] at s1 s2 ⊢
      exact morseReach_trans s1 s2
    · have s1 := morseReach_procBeads_frame (List.replicate t₀ .t ++ isoCurlStack w₀ ++ [.cs]) La
        _ _ (morseReach_procBeads_stackN w₁)
      have s2 := ih hLa' t₀ w₀ (w₁ - 1)
      have e3 : w₁ + isoBeadWr (.n :: La) + 2 * ((isoBeadCountT La : ℕ) : ℤ) =
          w₁ - 1 + isoBeadWr La + 2 * ((isoBeadCountT La : ℕ) : ℤ) := by
        simp only [isoBeadCountT, isoBeadWr, List.count_cons]
        simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte]; push_cast; ring
      have e1 : isoBeadCountT (.n :: La) = isoBeadCountT La := by simp [isoBeadCountT]
      rw [e1, e3]
      simp only [List.append_assoc, List.cons_append, List.nil_append] at s1 s2 ⊢
      exact morseReach_trans s1 s2
    · have s1 := morseReach_procBeads_frame (List.replicate t₀ .t ++ isoCurlStack w₀ ++ [.cs]) La
        _ _ (morseReach_procBeads_commStack .lp (morseReach_symm morseReach_isoPark_LPP)
          (morseReach_symm morseReach_isoPark_LPN) w₁)
      have s2 := morseReach_procBeads_frame (List.replicate t₀ .t ++ isoCurlStack w₀)
        (isoCurlStack w₁ ++ La) _ _ morseReach_isoPark_CSLP
      have s3 := morseReach_procBeads_frame (List.replicate t₀ .t ++ isoCurlStack w₀ ++ [.cs]) La
        _ _ (morseReach_procBeads_pStack w₁)
      have s4 := ih hLa' t₀ w₀ (w₁ + 1)
      have e3 : w₁ + isoBeadWr (.lp :: La) + 2 * ((isoBeadCountT La : ℕ) : ℤ) =
          w₁ + 1 + isoBeadWr La + 2 * ((isoBeadCountT La : ℕ) : ℤ) := by
        simp only [isoBeadCountT, isoBeadWr, List.count_cons]
        simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte]; push_cast; ring
      have e1 : isoBeadCountT (.lp :: La) = isoBeadCountT La := by
        simp [isoBeadCountT]
      rw [e1, e3]
      simp only [List.append_assoc, List.cons_append, List.nil_append] at s1 s2 s3 s4 ⊢
      exact morseReach_trans s1 <| morseReach_trans s2 <| morseReach_trans s3 s4


/-- Processing the beads before the clasp. -/
theorem morseReach_isoProc_before (Lb R : List IsoBead) (hLb : ∀ x ∈ Lb, IsoProcBead x)
    (t₀ : ℕ) (w₀ : ℤ) :
    MorseReach 2 (isoBeadsWord (Lb ++ List.replicate t₀ .t ++ isoCurlStack w₀ ++ [.cs] ++ R))
      (isoBeadsWord (List.replicate (t₀ + isoBeadCountT Lb) .t ++
        isoCurlStack (w₀ + isoBeadWr Lb) ++ [.cs] ++ R)) := by
  induction Lb using List.reverseRecOn generalizing t₀ w₀ with
  | nil => simpa [isoBeadCountT, isoBeadWr] using morseReach_refl 2 _
  | append_singleton L x ih =>
    have hL : ∀ y ∈ L, IsoProcBead y := fun y hy ↦ hLb y (List.mem_append_left _ hy)
    have hcT : ∀ y : IsoBead, isoBeadCountT (L ++ [y]) = isoBeadCountT L + isoBeadCountT [y] := by
      intro y; simp [isoBeadCountT, List.count_append]
    have hwr : ∀ y : IsoBead, isoBeadWr (L ++ [y]) = isoBeadWr L + isoBeadWr [y] := by
      intro y; simp only [isoBeadWr, List.count_append]; push_cast; ring
    rw [hcT, hwr]
    rcases hLb x (List.mem_append_right _ (List.mem_singleton_self x)) with rfl | rfl | rfl | rfl
    · have s1 := ih hL (t₀ + 1) w₀
      rw [List.replicate_succ] at s1
      have e1 : t₀ + (isoBeadCountT L + isoBeadCountT [.t]) = t₀ + 1 + isoBeadCountT L := by
        simp [isoBeadCountT]; ring
      have e2 : isoBeadWr [.t] = 0 := by simp [isoBeadWr]
      rw [e1, e2, add_zero]
      simp only [List.append_assoc, List.cons_append, List.nil_append] at s1 ⊢
      exact s1
    · have s1 := morseReach_procBeads_frame L (isoCurlStack w₀ ++ [.cs] ++ R) _ _
        (morseReach_symm (morseReach_procBeads_commRep .t .p morseReach_isoPark_TP t₀))
      have s2 := morseReach_procBeads_frame (L ++ List.replicate t₀ .t) ([.cs] ++ R) _ _
        (morseReach_procBeads_pStack w₀)
      have s3 := ih hL t₀ (w₀ + 1)
      have e1 : isoBeadCountT [.p] = 0 := by simp [isoBeadCountT]
      have e2 : w₀ + (isoBeadWr L + isoBeadWr [.p]) = w₀ + 1 + isoBeadWr L := by
        simp [isoBeadWr]; ring
      rw [e1, e2, add_zero]
      simp only [List.append_assoc, List.cons_append, List.nil_append] at s1 s2 s3 ⊢
      exact morseReach_trans s1 <| morseReach_trans s2 s3
    · have s1 := morseReach_procBeads_frame L (isoCurlStack w₀ ++ [.cs] ++ R) _ _
        (morseReach_symm (morseReach_procBeads_commRep .t .n
          (morseReach_symm morseReach_isoPark_NT) t₀))
      have s2 := morseReach_procBeads_frame (L ++ List.replicate t₀ .t) ([.cs] ++ R) _ _
        (morseReach_procBeads_nStack w₀)
      have s3 := ih hL t₀ (w₀ - 1)
      have e1 : isoBeadCountT [.n] = 0 := by simp [isoBeadCountT]
      have e2 : w₀ + (isoBeadWr L + isoBeadWr [.n]) = w₀ - 1 + isoBeadWr L := by
        simp [isoBeadWr]; ring
      rw [e1, e2, add_zero]
      simp only [List.append_assoc, List.cons_append, List.nil_append] at s1 s2 s3 ⊢
      exact morseReach_trans s1 <| morseReach_trans s2 s3
    · have s1 := morseReach_procBeads_frame L (isoCurlStack w₀ ++ [.cs] ++ R) _ _
        (morseReach_symm (morseReach_procBeads_commRep .t .lp
          (morseReach_symm morseReach_isoPark_LPT) t₀))
      have s2 := morseReach_procBeads_frame (L ++ List.replicate t₀ .t) ([.cs] ++ R) _ _
        (morseReach_symm (morseReach_procBeads_commStack .lp
          (morseReach_symm morseReach_isoPark_LPP) (morseReach_symm morseReach_isoPark_LPN) w₀))
      have s3 := morseReach_procBeads_frame (L ++ List.replicate t₀ .t ++ isoCurlStack w₀) R _ _
        morseReach_isoPark_LPCS
      have s4 := morseReach_procBeads_frame (L ++ List.replicate t₀ .t) ([.cs] ++ R) _ _
        (morseReach_procBeads_stackP w₀)
      have s5 := ih hL t₀ (w₀ + 1)
      have e1 : isoBeadCountT [.lp] = 0 := by simp [isoBeadCountT]
      have e2 : w₀ + (isoBeadWr L + isoBeadWr [.lp]) = w₀ + 1 + isoBeadWr L := by
        simp [isoBeadWr]; ring
      rw [e1, e2, add_zero]
      simp only [List.append_assoc, List.cons_append, List.nil_append] at s1 s2 s3 s4 s5 ⊢
      exact morseReach_trans s1 <| morseReach_trans s2 <| morseReach_trans s3 <|
        morseReach_trans s4 s5


/-- Processing a stack with one clasp. -/
theorem morseReach_isoProc (Lb La : List IsoBead) (hLb : ∀ x ∈ Lb, IsoProcBead x)
    (hLa : ∀ x ∈ La, IsoProcBead x) :
    MorseReach 2 (isoBeadsWord (Lb ++ [.cs] ++ La))
      (isoBeadsWord (List.replicate (isoBeadCountT Lb + isoBeadCountT La) .t ++
        isoCurlStack (isoBeadWr Lb - 2 * isoBeadCountT La) ++ [.cs] ++
        isoCurlStack (isoBeadWr La + 2 * isoBeadCountT La))) := by
  have h1 := morseReach_isoProc_before Lb La hLb 0 0
  have h2 := morseReach_isoProc_after La hLa (isoBeadCountT Lb) (isoBeadWr Lb) 0
  simp only [isoCurlStack_zero_proc, List.replicate_zero, List.append_nil, zero_add] at h1 h2
  exact morseReach_trans h1 h2


/-- A move between bead stacks can be done inside a longer stack. -/
theorem morseReach_isoBeads_frame (U V A B : List IsoBead)
    (h : MorseReach 2 (isoBeadsWord A) (isoBeadsWord B)) :
    MorseReach 2 (isoBeadsWord (U ++ A ++ V)) (isoBeadsWord (U ++ B ++ V)) :=
  morseReach_procBeads_frame U V A B h

/-- A curl stack passes a run of twists. -/
theorem morseReach_isoCurlStack_twists (w : ℤ) :
    ∀ c : ℕ, MorseReach 2 (isoBeadsWord (isoCurlStack w ++ List.replicate c .t))
      (isoBeadsWord (List.replicate c .t ++ isoCurlStack w))
  | 0 => by simpa using morseReach_refl 2 _
  | c + 1 => by
    have h1 := morseReach_procBeads_frame [] (List.replicate c .t) _ _
      (morseReach_procBeads_commStack .t (morseReach_symm morseReach_isoPark_TP)
        morseReach_isoPark_NT w)
    have h2 := morseReach_procBeads_frame [.t] [] _ _ (morseReach_isoCurlStack_twists w c)
    rw [List.replicate_succ]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- Opposite curl stacks cancel. -/
theorem morseReach_isoCurlStack_cancel (w : ℤ) :
    MorseReach 2 (isoBeadsWord (isoCurlStack w ++ isoCurlStack (-w))) (isoBeadsWord []) := by
  have hrep : ∀ (a b : IsoBead), MorseReach 2 (isoBeadsWord [a, b]) (isoBeadsWord []) →
      ∀ k : ℕ, MorseReach 2 (isoBeadsWord (List.replicate k a ++ List.replicate k b))
        (isoBeadsWord []) := by
    intro a b hab k
    induction k with
    | zero => exact morseReach_refl 2 _
    | succ k ih =>
      have h1 := morseReach_procBeads_frame (List.replicate k a) (List.replicate k b) _ _ hab
      rw [List.replicate_succ', List.replicate_succ]
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil] at h1 ih ⊢
      exact morseReach_trans h1 ih
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg w
  · rw [isoCurlStack_ofNat_proc, isoCurlStack_neg_proc]
    exact hrep _ _ morseReach_isoPark_PN k
  · rw [isoCurlStack_neg_proc, neg_neg, isoCurlStack_ofNat_proc]
    exact hrep _ _ morseReach_isoPark_NP k

/-- A curl stack consists of curls `p` and `n`. -/
theorem isoCurlStack_mem (w : ℤ) : ∀ x ∈ isoCurlStack w, x = .p ∨ x = .n := by
  intro x hx
  simp only [isoCurlStack] at hx
  split_ifs at hx
  · exact Or.inl (List.eq_of_mem_replicate hx)
  · exact Or.inr (List.eq_of_mem_replicate hx)

end AJConjecture
