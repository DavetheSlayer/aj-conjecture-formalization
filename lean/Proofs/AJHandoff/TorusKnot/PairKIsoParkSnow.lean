import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkHop
import AJHandoff.TorusKnot.PairKIsoParkOrbit

/-!
# Stage C by ports: the two snowballs

All beads are gathered at the port `r - 1`, where the clasp sits (`pairParkW1 → pairParkW3`).

* Forward snowball (`pairParkWF k`, `k = 0 … K*`): the bottom stack joins the port `q = a_0`
  (`morseReach_park_bottom`); then the whole stack of the port `a_k` hops to the port `a_{k+1}`
  (`morseReach_park_hop` with `X = []`) and lands under its stack. At `k = K*` it lands under
  the clasp at the port `a_{K*} = r - 1`. The ports `a_{k+1}` with `k + 1 < K*` are reached by
  left arcs (`a_{k+1} ≠ q, r - 1`).
* Backward snowball (`pairParkWB m`, `m = 1 … r - K*`): the top curl hops backward to the port
  `a_{r-1}` (`morseReach_park_hop` read backwards, the case `(a + s) mod r = q`), then the
  stack of the port `a_{r-m}` hops backward onto the top of the stack of `a_{r-m-1}`. At
  `m = r - K*` it lands on top of the port `r - 1`.

`pairParkWB (r - K*) = pairParkW3`: every port has been emptied into the port `r - 1`
(`pairParkA_inj`).
-/

namespace AJConjecture

/-- The port word depends only on the stacks of the ports `a < r`. -/
private theorem pairParkW_congr_snow (r s : ℕ) (bot top : List IsoBead)
    {S S' : ℕ → List IsoBead} (hS : ∀ a < r, S a = S' a) :
    pairParkW r s bot S top = pairParkW r s bot S' top := by
  simp only [pairParkW]
  rw [List.flatMap_congr fun a ha ↦ by rw [hS a (List.mem_range.1 ha)]]

/-- One hop to a port, for a stack `S` whose port `a` holds `X ++ L`. -/
private theorem morseReach_park_hopPort_snow {r s a : ℕ} (bot top X L : List IsoBead)
    (S : ℕ → List IsoBead) (hr : 3 ≤ r) (ha : a < r) (hab : (a + s) % r ≠ a)
    (hb : (a + s) % r ≠ r - 2) (hSa : S a = X ++ L) :
    MorseReach 1 (pairParkW r s bot S top) (pairParkW r s bot (Function.update
      (Function.update S a X) ((a + s) % r) (L ++ S ((a + s) % r))) top) := by
  have h := morseReach_park_hop r s a bot top X L S hr ha hab
  rw [ite_eq_right hb, ← hSa, Function.update_eq_self] at h
  exact h

/-- One hop to the top end, for a stack `S` whose port `a` holds `X ++ L`. -/
private theorem morseReach_park_hopTop_snow {r s a : ℕ} (bot top X L : List IsoBead)
    (S : ℕ → List IsoBead) (hr : 3 ≤ r) (ha : a < r) (hab : (a + s) % r ≠ a)
    (hb : (a + s) % r = r - 2) (hSa : S a = X ++ L) :
    MorseReach 1 (pairParkW r s bot S top)
      (pairParkW r s bot (Function.update S a X) (L ++ top)) := by
  have h := morseReach_park_hop r s a bot top X L S hr ha hab
  rw [ite_eq_left hb, ← hSa, Function.update_eq_self] at h
  exact h

/-- Every port is visited by the orbit. -/
private theorem pairParkA_surj_snow {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {a : ℕ}
    (ha : a < r) : ∃ k < r, pairParkA r s k = a := by
  have hr0 : 0 < r := by omega
  have hsub : (Finset.range r).image (pairParkA r s) ⊆ Finset.range r := fun x hx ↦ by
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (Nat.mod_lt _ hr0)
  have hcard : (Finset.range r).card ≤ ((Finset.range r).image (pairParkA r s)).card := by
    rw [Finset.card_image_of_injOn fun a ha b hb he ↦
      pairParkA_inj h hr (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) he]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have : a ∈ (Finset.range r).image (pairParkA r s) := by
    rw [heq]; exact Finset.mem_range.2 ha
  obtain ⟨k, hk, he⟩ := Finset.mem_image.1 this
  exact ⟨k, Finset.mem_range.1 hk, he⟩

/-- Membership in the first `k` ports of the orbit. -/
private theorem any_range_pairParkA_snow (r s k c : ℕ) :
    ((List.range k).any (fun j ↦ pairParkA r s j = c)) = true ↔
      ∃ j < k, pairParkA r s j = c := by
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]

/-- Membership in the ports `a_{b}, …, a_{b+m-1}` of the orbit. -/
private theorem any_range_pairParkA_add_snow (r s b m c : ℕ) :
    ((List.range m).any (fun i ↦ pairParkA r s (b + i) = c)) = true ↔
      ∃ i < m, pairParkA r s (b + i) = c := by
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]

/-- The bottom hop. -/
theorem morseReach_pairParkW1_WF0 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairParkW1 r s) (pairParkWF r s 0) := by
  have h0 := (pairParkA_succ h hr 0).2.1
  have e : pairParkSF r s 0 =
      Function.update (pairParkS1 r s) (r - 2) ([.t, .n] ++ pairParkS1 r s (r - 2)) := by
    funext c
    by_cases hc : c = r - 2
    · subst hc
      simp [pairParkSF, pairParkSnowF, h0]
    · simp [pairParkSF, h0, hc]
  rw [pairParkWF, e]
  exact morseReach_park_bottom r s [.t, .n] [.p] (pairParkS1 r s) hr

/-- One forward hop of the snowball. -/
theorem morseReach_pairParkWF_succ {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {k : ℕ}
    (hk : k < pairParkKs r s) :
    MorseReach 1 (pairParkWF r s k) (pairParkWF r s (k + 1)) := by
  obtain ⟨-, hKr, -, -⟩ := pairParkKs_spec h hr
  obtain ⟨hA1, -, -, hAq, hAr, hAs⟩ := pairParkA_succ h hr k
  have hb : (pairParkA r s k + s) % r ≠ r - 2 := by
    rw [← hA1]; exact (pairParkA_succ h hr (k + 1)).2.2.2.1 (by omega) (by omega)
  have hinj : ∀ j < r, ∀ j' < r, pairParkA r s j = pairParkA r s j' → j = j' :=
    fun j hj j' hj' he ↦ pairParkA_inj h hr hj hj' he
  have h1 := morseReach_park_hopPort_snow [] [.p] [] (pairParkSnowF r s k) (pairParkSF r s k) hr
    hAr hAs hb (by simp [pairParkSF])
  rw [← hA1] at h1
  rw [pairParkWF, pairParkWF]
  convert h1 using 2
  funext c
  by_cases hc1 : c = pairParkA r s (k + 1)
  · subst hc1
    have hne : pairParkA r s (k + 1) ≠ pairParkA r s k := fun he ↦ by
      have := hinj _ (by omega) _ (by omega) he; omega
    have hnot : ¬ ∃ j < k, pairParkA r s j = pairParkA r s (k + 1) := fun ⟨j, hj, he⟩ ↦ by
      have := hinj _ (by omega) _ (by omega) he; omega
    have e : pairParkSF r s k (pairParkA r s (k + 1)) = pairParkS1 r s (pairParkA r s (k + 1)) := by
      rw [pairParkSF, ite_eq_right hne, ite_eq_right (by rwa [any_range_pairParkA_snow])]
    rw [Function.update_self, e, pairParkSF, ite_eq_left rfl, pairParkSnowF, pairParkSnowF,
      List.range_succ, List.flatMap_append]
    simp
  · by_cases hc0 : c = pairParkA r s k
    · subst hc0
      rw [Function.update_of_ne hc1, Function.update_self, pairParkSF, ite_eq_right hc1,
        ite_eq_left ((any_range_pairParkA_snow r s (k + 1) _).2 ⟨k, by omega, rfl⟩)]
    · have hiff : (∃ j < k + 1, pairParkA r s j = c) ↔ ∃ j < k, pairParkA r s j = c := by
        constructor
        · rintro ⟨j, hj, he⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact ⟨j, hj, he⟩
          · exact absurd he.symm hc0
        · rintro ⟨j, hj, he⟩; exact ⟨j, by omega, he⟩
      simp only [pairParkSF, Function.update_apply, hc1, hc0, ite_false, any_range_pairParkA_snow,
        hiff]

/-- The top curl hops backward to the port `a_{r-1}`. -/
theorem morseReach_pairParkWF_WB1 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairParkWF r s (pairParkKs r s)) (pairParkWB r s 1) := by
  obtain ⟨hA1, -, hAr0, -, hAr, hAs⟩ := pairParkA_succ h hr (r - 1)
  have hq : (pairParkA r s (r - 1) + s) % r = r - 2 := by
    rw [← hA1, show r - 1 + 1 = r by omega, hAr0]
  have e1 : pairParkSB r s 1 (pairParkA r s (r - 1)) =
      pairParkSF r s (pairParkKs r s) (pairParkA r s (r - 1)) ++ [.p] := by
    simp [pairParkSB, pairParkSnowB]
  have h1 := morseReach_park_hopTop_snow [] [] _ [.p] (pairParkSB r s 1) hr hAr hAs hq e1
  have e2 : Function.update (pairParkSB r s 1) (pairParkA r s (r - 1))
      (pairParkSF r s (pairParkKs r s) (pairParkA r s (r - 1))) =
        pairParkSF r s (pairParkKs r s) := by
    funext c
    by_cases hc : c = pairParkA r s (r - 1)
    · subst hc; simp
    · simp [pairParkSB, hc]
  rw [e2] at h1
  rw [pairParkWF, pairParkWB]
  simpa using morseReach_symm h1

/-- One backward hop of the snowball. -/
theorem morseReach_pairParkWB_succ {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {m : ℕ}
    (hm1 : 1 ≤ m) (hm : m < r - pairParkKs r s) :
    MorseReach 1 (pairParkWB r s m) (pairParkWB r s (m + 1)) := by
  obtain ⟨hK1, hKr, hKA, -⟩ := pairParkKs_spec h hr
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨hA1, -, -, -, hAr, hAs⟩ := pairParkA_succ h hr (r - (m + 1 + 1))
  have hb_eq : (pairParkA r s (r - (m + 1 + 1)) + s) % r = pairParkA r s (r - (m + 1)) := by
    rw [← hA1]; congr 1; omega
  have hb : (pairParkA r s (r - (m + 1 + 1)) + s) % r ≠ r - 2 := by
    rw [hb_eq]; exact (pairParkA_succ h hr (r - (m + 1))).2.2.2.1 (by omega) (by omega)
  have hinj : ∀ j < r, ∀ j' < r, pairParkA r s j = pairParkA r s j' → j = j' :=
    fun j hj j' hj' he ↦ pairParkA_inj h hr hj hj' he
  have e1 : pairParkSB r s (m + 1 + 1) (pairParkA r s (r - (m + 1 + 1))) =
      pairParkSF r s (pairParkKs r s) (pairParkA r s (r - (m + 1 + 1))) ++
        pairParkSnowB r s (m + 1 + 1) := by
    rw [pairParkSB, ite_eq_left rfl]
  have h1 := morseReach_park_hopPort_snow [] [] _ _ (pairParkSB r s (m + 1 + 1)) hr hAr hAs hb e1
  rw [hb_eq] at h1
  apply morseReach_symm
  rw [pairParkWB, pairParkWB]
  convert h1 using 2
  have hab : pairParkA r s (r - (m + 1)) ≠ pairParkA r s (r - (m + 1 + 1)) := fun he ↦ by
    have := hinj _ (by omega) _ (by omega) he; omega
  have hSBb : pairParkSB r s (m + 1 + 1) (pairParkA r s (r - (m + 1))) = [] := by
    rw [pairParkSB, ite_eq_right hab, ite_eq_left ((any_range_pairParkA_add_snow r s
      (r - (m + 1 + 1) + 1) (m + 1 + 1 - 1) _).2 ⟨0, by omega, by congr 1; omega⟩)]
  have hSFb : pairParkSF r s (pairParkKs r s) (pairParkA r s (r - (m + 1))) =
      pairParkS1 r s (pairParkA r s (r - (m + 1))) := by
    have h1 : pairParkA r s (r - (m + 1)) ≠ pairParkA r s (pairParkKs r s) := fun he ↦ by
      have := hinj _ (by omega) _ (by omega) he; omega
    have h2 : ¬ ∃ j < pairParkKs r s, pairParkA r s j = pairParkA r s (r - (m + 1)) :=
      fun ⟨j, hj, he⟩ ↦ by have := hinj _ (by omega) _ (by omega) he; omega
    rw [pairParkSF, ite_eq_right h1, ite_eq_right (by rwa [any_range_pairParkA_snow])]
  have hSnow : pairParkSnowB r s (m + 1 + 1) =
      pairParkS1 r s (pairParkA r s (r - (m + 1))) ++ pairParkSnowB r s (m + 1) := by
    simp only [pairParkSnowB, Nat.add_sub_cancel, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map, List.append_assoc]
    rw [show r - (m + 1 + 1) + 1 + 0 = r - (m + 1) by omega]
    congr 2
    exact List.flatMap_congr fun i _ ↦ by
      simp only [Nat.succ_eq_add_one]
      congr 2
      omega
  funext c
  by_cases hcb : c = pairParkA r s (r - (m + 1))
  · subst hcb
    rw [Function.update_self, hSBb, List.append_nil, hSnow, pairParkSB, ite_eq_left rfl, hSFb]
  · by_cases hca : c = pairParkA r s (r - (m + 1 + 1))
    · subst hca
      have hn : ¬ ∃ i < m + 1 - 1, pairParkA r s (r - (m + 1) + 1 + i) =
          pairParkA r s (r - (m + 1 + 1)) := fun ⟨i, hi, he⟩ ↦ by
        have := hinj _ (by omega) _ (by omega) he; omega
      rw [Function.update_of_ne hcb, Function.update_self, pairParkSB, ite_eq_right hcb,
        ite_eq_right (by rwa [any_range_pairParkA_add_snow])]
    · have hiff : ((List.range (m + 1 - 1)).any
            (fun i ↦ pairParkA r s (r - (m + 1) + 1 + i) = c)) =
          ((List.range (m + 1 + 1 - 1)).any
            (fun i ↦ pairParkA r s (r - (m + 1 + 1) + 1 + i) = c)) := by
        rw [Bool.eq_iff_iff, any_range_pairParkA_add_snow, any_range_pairParkA_add_snow]
        constructor
        · rintro ⟨i, hi, he⟩
          exact ⟨i + 1, by omega, by rw [← he]; congr 1; omega⟩
        · rintro ⟨i, hi, he⟩
          rcases i with _ | i
          · exact absurd (by rw [← he]; congr 1; omega) hcb
          · exact ⟨i, by omega, by rw [← he]; congr 1; omega⟩
      rw [Function.update_of_ne hcb, Function.update_of_ne hca, pairParkSB, pairParkSB,
        ite_eq_right hcb, ite_eq_right hca, hiff]

/-- After both snowballs everything is at the port `r - 1`. -/
theorem pairParkWB_last {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    pairParkWB r s (r - pairParkKs r s) = pairParkW3 r s := by
  obtain ⟨hK1, hKr, hKA, -⟩ := pairParkKs_spec h hr
  have hinj : ∀ j < r, ∀ j' < r, pairParkA r s j = pairParkA r s j' → j = j' :=
    fun j hj j' hj' he ↦ pairParkA_inj h hr hj hj' he
  have hKs' : r - (r - pairParkKs r s) = pairParkKs r s := by omega
  rw [pairParkWB, pairParkW3]
  apply pairParkW_congr_snow
  intro c hc
  by_cases hc1 : c = r - 1
  · subst hc1
    have hsplit : ∀ (a b : ℕ) (f : ℕ → List IsoBead), (List.range (a + b)).flatMap f =
        (List.range a).flatMap f ++ (List.range b).flatMap (fun i ↦ f (a + i)) := by
      intro a b f
      rw [List.range_add, List.flatMap_append, List.flatMap_map]
    have hs := hsplit (pairParkKs r s + 1) (r - pairParkKs r s - 1)
      (fun k ↦ pairParkS1 r s (pairParkA r s k))
    rw [show pairParkKs r s + 1 + (r - pairParkKs r s - 1) = r by omega] at hs
    rw [pairParkAt, ite_eq_left rfl, pairParkSB, hKs', ite_eq_left hKA.symm, pairParkSF,
      ite_eq_left hKA.symm, pairParkSigma, pairParkSnowF, pairParkSnowB, hKs', hs]
    simp only [List.append_assoc]
  · rw [pairParkAt, ite_eq_right hc1]
    obtain ⟨j, hj, rfl⟩ := pairParkA_surj_snow h hr hc
    have hjK : j ≠ pairParkKs r s := fun he ↦ hc1 (by rw [he, hKA])
    have hne : pairParkA r s j ≠ pairParkA r s (pairParkKs r s) := fun he ↦
      hjK (hinj _ hj _ hKr he)
    rw [pairParkSB, hKs', ite_eq_right hne]
    rcases Nat.lt_or_gt_of_ne hjK with hjlt | hjgt
    · have hSF : pairParkSF r s (pairParkKs r s) (pairParkA r s j) = [] := by
        rw [pairParkSF, ite_eq_right hne,
          ite_eq_left ((any_range_pairParkA_snow r s _ _).2 ⟨j, hjlt, rfl⟩)]
      split_ifs <;> first | rfl | exact hSF
    · rw [ite_eq_left ((any_range_pairParkA_add_snow r s _ _ _).2
        ⟨j - pairParkKs r s - 1, by omega, by congr 1; omega⟩)]

/-- A clean journey to the top end: the top part `L` of the port `a_k` hops forward through the
empty ports `a_{k+1}, …, a_{r-1}` and reaches the top end. -/
theorem morseReach_park_cleanToTop {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    ∀ (n k : ℕ), r - 1 - k = n → k < r →
      ∀ (bot top X L : List IsoBead) (S : ℕ → List IsoBead),
      (∀ j, k < j → j < r → S (pairParkA r s j) = []) → S (pairParkA r s k) = X ++ L →
      MorseReach 1 (pairParkW r s bot S top)
        (pairParkW r s bot (Function.update S (pairParkA r s k) X) (L ++ top)) := by
  intro n
  induction n with
  | zero =>
    intro k hn hk bot top X L S _ hSk
    obtain ⟨hA1, -, hAr0, -, hAr, hAs⟩ := pairParkA_succ h hr k
    have hq : (pairParkA r s k + s) % r = r - 2 := by
      rw [← hA1, show k + 1 = r by omega, hAr0]
    exact morseReach_park_hopTop_snow bot top X L S hr hAr hAs hq hSk
  | succ n ih =>
    intro k hn hk bot top X L S hS hSk
    obtain ⟨hA1, -, -, -, hAr, hAs⟩ := pairParkA_succ h hr k
    have hb : (pairParkA r s k + s) % r ≠ r - 2 := by
      rw [← hA1]; exact (pairParkA_succ h hr (k + 1)).2.2.2.1 (by omega) (by omega)
    have hne : pairParkA r s (k + 1) ≠ pairParkA r s k := fun he ↦ by
      have := pairParkA_inj h hr (by omega) hk he; omega
    have h1 := morseReach_park_hopPort_snow bot top X L S hr hAr hAs hb hSk
    rw [← hA1, hS (k + 1) (by omega) (by omega)] at h1
    have h2 := ih (k + 1) (by omega) (by omega) bot top [] L
      (Function.update (Function.update S (pairParkA r s k) X) (pairParkA r s (k + 1)) (L ++ []))
      (fun j hj1 hj2 ↦ by
        have h1' : pairParkA r s j ≠ pairParkA r s (k + 1) := fun he ↦ by
          have := pairParkA_inj h hr (by omega) (by omega) he; omega
        have h2' : pairParkA r s j ≠ pairParkA r s k := fun he ↦ by
          have := pairParkA_inj h hr (by omega) hk he; omega
        rw [Function.update_of_ne h1', Function.update_of_ne h2', hS j (by omega) hj2])
      (by rw [Function.update_self, List.append_nil, List.nil_append])
    have e : Function.update (Function.update S (pairParkA r s k) X) (pairParkA r s (k + 1)) [] =
        Function.update S (pairParkA r s k) X := Function.update_eq_self_iff.2
      (by rw [Function.update_of_ne hne, hS (k + 1) (by omega) (by omega)])
    rw [Function.update_idem, e] at h2
    exact morseReach_trans h1 h2

/-- A clean journey to a port: the top part `L` of the port `a_j` hops forward through the empty
ports `a_{j+1}, …, a_{k-1}` and lands at the bottom of the stack of the port `a_k`. -/
theorem morseReach_park_cleanToPort {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    ∀ (n j k : ℕ), k - j - 1 = n → j < k → k < r →
      ∀ (bot top X L : List IsoBead) (S : ℕ → List IsoBead),
      (∀ i, j < i → i < k → S (pairParkA r s i) = []) → S (pairParkA r s j) = X ++ L →
      MorseReach 1 (pairParkW r s bot S top)
        (pairParkW r s bot (Function.update (Function.update S (pairParkA r s j) X)
          (pairParkA r s k) (L ++ S (pairParkA r s k))) top) := by
  intro n
  induction n with
  | zero =>
    intro j k hn hjk hk bot top X L S _ hSj
    obtain ⟨hA1, -, -, -, hAr, hAs⟩ := pairParkA_succ h hr j
    have hb : (pairParkA r s j + s) % r ≠ r - 2 := by
      rw [← hA1]; exact (pairParkA_succ h hr (j + 1)).2.2.2.1 (by omega) (by omega)
    have h1 := morseReach_park_hopPort_snow bot top X L S hr hAr hAs hb hSj
    rwa [← hA1, show j + 1 = k by omega] at h1
  | succ n ih =>
    intro j k hn hjk hk bot top X L S hS hSj
    obtain ⟨hA1, -, -, -, hAr, hAs⟩ := pairParkA_succ h hr j
    have hb : (pairParkA r s j + s) % r ≠ r - 2 := by
      rw [← hA1]; exact (pairParkA_succ h hr (j + 1)).2.2.2.1 (by omega) (by omega)
    have hinj : ∀ a < r, ∀ b < r, pairParkA r s a = pairParkA r s b → a = b :=
      fun a ha b hb he ↦ pairParkA_inj h hr ha hb he
    have hne : pairParkA r s (j + 1) ≠ pairParkA r s j := fun he ↦ by
      have := hinj _ (by omega) _ (by omega) he; omega
    have h1 := morseReach_park_hopPort_snow bot top X L S hr hAr hAs hb hSj
    rw [← hA1, hS (j + 1) (by omega) (by omega)] at h1
    have h2 := ih (j + 1) k (by omega) (by omega) hk bot top [] L
      (Function.update (Function.update S (pairParkA r s j) X) (pairParkA r s (j + 1)) (L ++ []))
      (fun i hi1 hi2 ↦ by
        have h1' : pairParkA r s i ≠ pairParkA r s (j + 1) := fun he ↦ by
          have := hinj _ (by omega) _ (by omega) he; omega
        have h2' : pairParkA r s i ≠ pairParkA r s j := fun he ↦ by
          have := hinj _ (by omega) _ (by omega) he; omega
        rw [Function.update_of_ne h1', Function.update_of_ne h2', hS i (by omega) hi2])
      (by rw [Function.update_self, List.append_nil, List.nil_append])
    have hk1 : pairParkA r s k ≠ pairParkA r s (j + 1) := fun he ↦ by
      have := hinj _ (by omega) _ (by omega) he; omega
    have hk0 : pairParkA r s k ≠ pairParkA r s j := fun he ↦ by
      have := hinj _ (by omega) _ (by omega) he; omega
    have e : Function.update (Function.update S (pairParkA r s j) X) (pairParkA r s (j + 1)) [] =
        Function.update S (pairParkA r s j) X := Function.update_eq_self_iff.2
      (by rw [Function.update_of_ne hne, hS (j + 1) (by omega) (by omega)])
    rw [Function.update_of_ne hk1, Function.update_of_ne hk0, Function.update_idem, e] at h2
    exact morseReach_trans h1 h2

end AJConjecture
