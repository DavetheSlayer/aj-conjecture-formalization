import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkHop
import AJHandoff.TorusKnot.PairKIsoParkOrbit

/-!
# Stage C by ports: journeys to the top end (used by stages G and E)

* `morseReach_park_portToTop`: the top part of the stack of the port `r - 1` (the only occupied
  port) travels forward through the empty ports `a_{K*+1}, …, a_{r-1}` to the top end
  (`morseReach_park_hop`, induction on the hops along the orbit, `pairParkA_succ`). Stage G uses
  it for the clasp (`pairWC → pairWG1`, after `pairWC ← pairParkW8`).
* `morseReach_park_bottomToTop`: a bottom stack travels along the whole knot to the top end
  (`morseReach_park_bottom`, then `r` hops through empty ports). Stage G uses it for the twists
  (`pairWG1 → pairWG2`), stage E for the travelling curl (`pairWE3 → pairWE4`).
* `pairParkW_empty`: with all ports empty the port word is `[u1] · bot · morseDouble (pairCore) ·
  top · [n1]`.
-/

namespace AJConjecture

/-- The twist stack as half twists. -/
theorem isoBeadsWord_replicate_t (c : ℕ) :
    isoBeadsWord (List.replicate c .t) = List.replicate (2 * c) (isoX false 0) := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [List.replicate_succ, show 2 * (c + 1) = 2 + 2 * c by ring, List.replicate_add]
    simp only [isoBeadsWord, List.flatMap_cons] at ih ⊢
    rw [ih]
    rfl

/-- With all ports empty the port word is the doubled core between the end stacks. -/
theorem pairParkW_empty (r s : ℕ) (bot top : List IsoBead) :
    pairParkW r s bot (fun _ ↦ []) top =
      [isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCore r s) ++ isoBeadsWord top ++
        [isoN 1] := by
  have hS : (List.range r).flatMap
      (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord ([] : List IsoBead))) = [] := by
    simp [isoBeadsWord, morseShiftWord]
  simp only [pairParkW, hS, pairCore_eq_parts, morseDouble, List.flatMap_append,
    List.append_nil, List.append_assoc]

/-- A stack at the port `a_k` travels through the empty ports `a_{k+1}, …, a_{r-1}` to the top
end. -/
private theorem morseReach_park_journeyTop {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r)
    (bot top L : List IsoBead) (P : ℕ → List IsoBead) :
    ∀ m k : ℕ, k + m = r - 1 → (∀ i, k < i → i < r → P (pairParkA r s i) = []) →
      MorseReach 1 (pairParkW r s bot (Function.update P (pairParkA r s k)
        (P (pairParkA r s k) ++ L)) top) (pairParkW r s bot P (L ++ top)) := by
  intro m
  induction m with
  | zero =>
    intro k hk _
    obtain ⟨h1, -, h3, -, h5, h6⟩ := pairParkA_succ h hr k
    have hh := morseReach_park_hop r s (pairParkA r s k) bot top (P (pairParkA r s k)) L P hr h5 h6
    have hA : (pairParkA r s k + s) % r = r - 2 := by
      rw [← h1, show k + 1 = r by omega, h3]
    simp only [hA, ↓reduceIte, Function.update_eq_self] at hh
    exact hh
  | succ m ih =>
    intro k hk hP
    obtain ⟨h1, -, -, -, h5, h6⟩ := pairParkA_succ h hr k
    have hh := morseReach_park_hop r s (pairParkA r s k) bot top (P (pairParkA r s k)) L P hr h5 h6
    have hA : (pairParkA r s k + s) % r ≠ r - 2 := by
      rw [← h1]; exact (pairParkA_succ h hr (k + 1)).2.2.2.1 (by omega) (by omega)
    simp only [hA, ↓reduceIte, Function.update_eq_self] at hh
    rw [← h1, hP (k + 1) (by omega) (by omega), List.append_nil] at hh
    have ih' := ih (k + 1) (by omega) (fun i hi hi' ↦ hP i (by omega) hi')
    rw [hP (k + 1) (by omega) (by omega), List.nil_append] at ih'
    exact morseReach_trans hh ih'

/-- The top part of the stack of the port `r - 1` travels to the top end. -/
theorem morseReach_park_portToTop {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r)
    (bot top X L : List IsoBead) :
    MorseReach 1 (pairParkW r s bot (pairParkAt r (X ++ L)) top)
      (pairParkW r s bot (pairParkAt r X) (L ++ top)) := by
  obtain ⟨hK1, hKr, hKa, hKu⟩ := pairParkKs_spec h hr
  have hj := morseReach_park_journeyTop h hr bot top L (pairParkAt r X) (r - 1 - pairParkKs r s)
    (pairParkKs r s) (by omega) (fun i hi hi' ↦ by
      have hne : pairParkA r s i ≠ r - 1 := fun he ↦ by have := hKu i hi' he; omega
      simp only [pairParkAt, hne, ↓reduceIte])
  have hS : Function.update (pairParkAt r X) (pairParkA r s (pairParkKs r s))
      (pairParkAt r X (pairParkA r s (pairParkKs r s)) ++ L) = pairParkAt r (X ++ L) := by
    funext a
    rw [hKa]
    by_cases ha : a = r - 1
    · subst ha; simp [pairParkAt]
    · rw [Function.update_of_ne ha]; simp [pairParkAt, ha]
  rw [hS] at hj
  exact hj

/-- A bottom stack travels along the whole knot to the top end. -/
theorem morseReach_park_bottomToTop {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r)
    (L top : List IsoBead) :
    MorseReach 1 (pairParkW r s L (fun _ ↦ []) top) (pairParkW r s [] (fun _ ↦ []) (L ++ top)) := by
  have hb := morseReach_park_bottom r s L top (fun _ ↦ []) hr
  have hj := morseReach_park_journeyTop h hr [] top L (fun _ ↦ []) (r - 1) 0 (by omega)
    (fun _ _ _ ↦ rfl)
  rw [(pairParkA_succ h hr 0).2.1, List.nil_append] at hj
  rw [List.append_nil] at hb
  exact morseReach_trans hb hj

end AJConjecture
