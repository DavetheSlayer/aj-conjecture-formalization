import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkNormDefs
import AJHandoff.TorusKnot.PairKIsoParkPorts

/-!
# Stage C by ports, normalisation step 3: the round curls to the ports

`morseReach_park_roundCurls`: in a port word whose middle is `ℓ` doubled rounds followed by `m`
doubled rounds each followed by a curl `p` on the band `q` (index `0`), the curls ride the
conveyor backwards to the ports: the curl after the `(ℓ + i)`-th round is on the index `0` at the
level `ℓ + i` and reaches the port `a` with `a + ℓ + i ≡ 0 (mod r)` (`morseReach_park_conv` read
backwards, on top of the port stack: all ports lie below the rounds). Induction on `m`.

With `ℓ = 1`, `m = s - 2` and one more round after them this is `pairParkV2 → pairParkW1`
(`pairRho r s a` counts the curls landing at the port `a`).
-/

namespace AJConjecture

/-- The number of curls landing at the port `a`. -/
def pairRhoAux (r ℓ m a : ℕ) : ℕ := ((List.range m).filter (fun i ↦ (a + ℓ + i + 1) % r = 0)).length

/-- A port word with an arbitrary middle depends only on the stacks of the ports `0 … r - 1`. -/
private theorem pairParkWX_congr_round (r : ℕ) (bot top : List IsoBead) (S S' : ℕ → List IsoBead)
    (mid : MorseWord) (h : ∀ a < r, S a = S' a) :
    pairParkWX r bot S mid top = pairParkWX r bot S' mid top := by
  have e : (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) =
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S' c))) :=
    List.flatMap_congr fun c hc ↦ by rw [h c (List.mem_range.1 hc)]
  simp only [pairParkWX, e]

/-- The port of a curl after `t` rounds on the index `0`. -/
private theorem exists_port_round (r t : ℕ) (hr : 3 ≤ r) :
    ∃ a < r, (a + t) % r = 0 ∧ ∀ c < r, (c + t) % r = 0 → c = a := by
  refine ⟨(r - t % r) % r, Nat.mod_lt _ (by omega), ?_, ?_⟩
  · have ht : t % r < r := Nat.mod_lt _ (by omega)
    rw [Nat.add_mod, Nat.mod_mod]
    rcases Nat.eq_zero_or_pos (t % r) with h0 | h0
    · rw [h0, Nat.sub_zero, Nat.mod_self]; simp
    · rw [Nat.mod_eq_of_lt (show r - t % r < r by omega), show r - t % r + t % r = r by omega,
        Nat.mod_self]
  · intro c hc hct
    have ht : t % r < r := Nat.mod_lt _ (by omega)
    rw [Nat.add_mod, Nat.mod_eq_of_lt hc] at hct
    rcases Nat.lt_or_ge (c + t % r) r with h1 | h1
    · rw [Nat.mod_eq_of_lt h1] at hct
      have : t % r = 0 := by omega
      rw [this, Nat.sub_zero, Nat.mod_self]; omega
    · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at hct
      rw [Nat.mod_eq_of_lt (show r - t % r < r by omega)]; omega

/-- A curl on the index `0` after `t` doubled rounds rides back to the top of its port. -/
private theorem morseReach_park_curlBack (r t a : ℕ) (bot top : List IsoBead)
    (S : ℕ → List IsoBead) (mid : MorseWord) (hr : 3 ≤ r) (ha : a < r) (hat : (a + t) % r = 0) :
    MorseReach 1
      (pairParkWX r bot S (phaseTwoBlk (pairDRound r) t ++
        morseShiftWord (2 * (r - 2)) (isoBeadsWord [.p]) ++ mid) top)
      (pairParkWX r bot (Function.update S a (S a ++ [.p])) (phaseTwoBlk (pairDRound r) t ++ mid)
        top) := by
  have hT := morseFits_isoBeadsWord [.p] 0
  have hP := morseFits_portW_all_park r S (List.range r) (fun c hc ↦ List.mem_range.1 hc) hr
  have hpre : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c)))) =
      4 * r - 1 := by
    rw [morseOut_append, morseOut_park_prefix r bot hr, hP.2]
  -- 1. back through the rounds
  have h1 := morseReach_park_conv 1 r a t (isoBeadsWord [.p])
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++
      (List.range r).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))))
    (mid ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1]) hr ha hT.1 hT.2
    (by rw [hpre]; omega)
  rw [hat, Nat.add_zero, morseDouble_phaseTwoBlk] at h1
  -- 2. back past the ports above `a`
  rw [portW_split_park r a S ha] at h1
  set A := (List.range a).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c)))
  set C := ((List.range (r - 1 - a)).map (fun i ↦ a + 1 + i)).flatMap
    (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c)))
  have hA := morseFits_portW_all_park r S (List.range a) (fun c hc ↦ by simp at hc; omega) hr
  have hC := morseFits_portW_all_park r S ((List.range (r - 1 - a)).map (fun i ↦ a + 1 + i))
    (fun c hc ↦ by simp at hc; omega) hr
  have hX := morseFits_port_one_park r a (S a) ha hr
  have hu : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++ A ++
      morseShiftWord (2 * (r - 2 + a)) (isoBeadsWord (S a))) = 4 * r - 1 := by
    rw [morseOut_append, morseOut_append, morseOut_park_prefix r bot hr, hA.2, hX.2]
  have h2 := morseReach_isoBead_commR 1 (2 * (r - 2 + a)) 2 (isoBeadsWord [.p])
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++ A ++
      morseShiftWord (2 * (r - 2 + a)) (isoBeadsWord (S a))) C
    (phaseTwoBlk (pairDRound r) t ++ mid ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++
      [isoN 1]) hT.1 hT.2
    (fun l hl ↦ by
      obtain ⟨c, hc, hl⟩ := mem_portW_park hl
      simp at hc; omega)
    (by rw [hu]; exact hC.1) (by rw [hu]; omega)
  rw [pairParkWX, pairParkWX, portW_update_split_park r a S _ ha, portW_split_park r a S ha,
    isoBeadsWord_append_park, morseShiftWord_append]
  simp only [pairDRound, List.append_assoc] at h1 h2 ⊢
  exact morseReach_trans (morseReach_symm h1) (morseReach_symm h2)

/-- The round curls ride back to the ports. -/
theorem morseReach_park_roundCurls (r ℓ m : ℕ) (bot top : List IsoBead) (S : ℕ → List IsoBead)
    (mid : MorseWord) (hr : 3 ≤ r) :
    MorseReach 1
      (pairParkWX r bot S (phaseTwoBlk (pairDRound r) ℓ ++
        phaseTwoBlk (pairDRound r ++ morseShiftWord (2 * (r - 2)) (isoBeadsWord [.p])) m ++ mid)
        top)
      (pairParkWX r bot (fun a ↦ S a ++ List.replicate (pairRhoAux r ℓ m a) .p)
        (phaseTwoBlk (pairDRound r) (ℓ + m) ++ mid) top) := by
  induction m generalizing mid with
  | zero =>
    have e : (fun a ↦ S a ++ List.replicate (pairRhoAux r ℓ 0 a) .p) = S := by
      funext a; simp [pairRhoAux]
    rw [e]
    simpa [phaseTwoBlk] using morseReach_refl 1 _
  | succ m ih =>
    have eB : phaseTwoBlk (pairDRound r ++ morseShiftWord (2 * (r - 2)) (isoBeadsWord [.p]))
        (m + 1) = phaseTwoBlk (pairDRound r ++ morseShiftWord (2 * (r - 2)) (isoBeadsWord [.p])) m ++
          (pairDRound r ++ morseShiftWord (2 * (r - 2)) (isoBeadsWord [.p])) := by
      simp [phaseTwoBlk, List.replicate_succ']
    have eB2 : phaseTwoBlk (pairDRound r) (ℓ + m) ++ pairDRound r =
        phaseTwoBlk (pairDRound r) (ℓ + m + 1) := by
      simp [phaseTwoBlk, List.replicate_succ']
    have h1 := ih (pairDRound r ++ morseShiftWord (2 * (r - 2)) (isoBeadsWord [.p]) ++ mid)
    obtain ⟨a, ha, hat, huniq⟩ := exists_port_round r (ℓ + m + 1) hr
    have h2 := morseReach_park_curlBack r (ℓ + m + 1) a bot top
      (fun a ↦ S a ++ List.replicate (pairRhoAux r ℓ m a) .p) mid hr ha hat
    rw [← eB2] at h2
    have hS : ∀ c < r, Function.update (fun a ↦ S a ++ List.replicate (pairRhoAux r ℓ m a) .p) a
        (S a ++ List.replicate (pairRhoAux r ℓ m a) .p ++ [.p]) c =
        S c ++ List.replicate (pairRhoAux r ℓ (m + 1) c) .p := by
      intro c hc
      have hρ : pairRhoAux r ℓ (m + 1) c = pairRhoAux r ℓ m c +
          if (c + ℓ + m + 1) % r = 0 then 1 else 0 := by
        simp only [pairRhoAux, List.range_succ, List.filter_append, List.length_append,
          List.filter_cons, List.filter_nil, decide_eq_true_eq]
        split_ifs <;> rfl
      by_cases hca : c = a
      · subst hca
        have h0 : (c + ℓ + m + 1) % r = 0 := by rw [← hat]; congr 1; ring
        rw [Function.update_self, hρ]
        simp only [h0, ↓reduceIte]
        rw [List.replicate_succ', List.append_assoc]
      · have h0 : ¬ (c + ℓ + m + 1) % r = 0 := fun h0 ↦ hca (huniq c hc (by
          rw [← h0]; congr 1; ring))
        rw [Function.update_of_ne hca, hρ]
        simp only [h0, ↓reduceIte, Nat.add_zero]
    rw [pairParkWX_congr_round r bot top _ _ _ hS] at h2
    rw [eB, show ℓ + (m + 1) = ℓ + m + 1 by ring, ← eB2]
    simp only [List.append_assoc] at h1 h2 ⊢
    exact morseReach_trans h1 h2


/-- Normalisation step 3. -/
theorem morseReach_pairParkV2_W1 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairParkV2 r s) (pairParkW1 r s) := by
  have hs : 2 ≤ s := by have := h.2.1; omega
  have h1 := morseReach_park_roundCurls r 1 (s - 2) [.t, .n] [.p] (pairParkS2 r s)
    (pairDRound r) hr
  have e1 : phaseTwoBlk (pairDRound r) 1 = pairDRound r := by simp [phaseTwoBlk]
  have e2 : phaseTwoBlk (pairDRound r) (1 + (s - 2)) ++ pairDRound r =
      morseDouble (pairConv r s) := by
    rw [pairConv, morseDouble_phaseTwoBlk, ← pairDRound]
    simp only [phaseTwoBlk, ← List.flatten_concat, ← List.replicate_succ']
    congr 2
    omega
  have e3 : ∀ a < r, pairParkS2 r s a ++ List.replicate (pairRhoAux r 1 (s - 2) a) .p =
      pairParkS1 r s a := by
    intro a _
    have hρ : pairRhoAux r 1 (s - 2) a = pairRho r s a := by
      simp only [pairRhoAux, pairRho]
      congr 2
      funext i
      rw [show a + 1 + i + 1 = i + 2 + a by omega]
    rw [hρ]
    simp only [pairParkS1, pairParkS2]
  rw [e1, e2, pairParkWX_congr_round r _ _ _ _ _ e3] at h1
  simpa only [pairParkV2, pairParkW1, pairParkW, pairParkWX, List.append_assoc] using h1


end AJConjecture
