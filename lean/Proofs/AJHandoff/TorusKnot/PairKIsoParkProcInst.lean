import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkProc
import AJHandoff.TorusKnot.PairKIsoParkOrbit
import AJHandoff.TorusKnot.PairKIsoParkPorts

/-!
# Stage C by ports: processing the collected stack (`pairParkW3 → pairParkW4`)

The stack at the port `r - 1` is `pairParkLb · cs · pairParkLa` (`pairParkSigma_split`). Its beads
are `t, p, n, lp` (the `ln` of the right descents were cancelled in the normalisation), with
`C = (r - 1) s` twists in all (`pairParkCount`: port `0` carries `z + 2`, the ports `1 … q - 1`
one each, the bottom and the port `r - 1` one each; every port is visited once by the orbit,
`pairParkA_inj`) and total curl writhe `0` (`pairParkWr`: `E + s + r = C + 3`). So
`morseReach_isoProc` turns it into `pairParkStack4`, and `morseReach_frame` (the port `r - 1` is
the band `2q + 1`) gives `pairParkW3 → pairParkW4`.
-/

namespace AJConjecture

/-- A move of the stack of one port (two strands) inside a port word. -/
private theorem morseReach_park_portLocal_inst (r s a : ℕ) (bot top A B : List IsoBead)
    (S : ℕ → List IsoBead) (hr : 3 ≤ r) (ha : a < r)
    (h : MorseReach 2 (isoBeadsWord A) (isoBeadsWord B)) :
    MorseReach 1 (pairParkW r s bot (Function.update S a A) top)
      (pairParkW r s bot (Function.update S a B) top) := by
  rw [pairParkW, pairParkW, portW_update_split_park r a S _ ha, portW_update_split_park r a S _ ha]
  set P := (List.range a).flatMap (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c)))
  have hP := morseFits_portW_all_park r S (List.range a) (fun c hc ↦ by simp at hc; omega) hr
  have hu : morseOut 1 ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++ P) =
      2 * (r - 2 + a) + 2 + (2 * r + 1 - 2 * a) := by
    rw [morseOut_append, morseOut_park_prefix r bot hr, hP.2]; omega
  have hf := morseReach_frame 2 1 (2 * (r - 2 + a)) (2 * r + 1 - 2 * a)
    ([isoU 1] ++ isoBeadsWord bot ++ morseDouble (pairCups r) ++ P)
    (((List.range (r - 1 - a)).map (fun i ↦ a + 1 + i)).flatMap
      (fun c ↦ morseShiftWord (2 * (r - 2 + c)) (isoBeadsWord (S c))) ++
      morseDouble (pairConv r s) ++ morseDouble (pairCaps r) ++ isoBeadsWord top ++ [isoN 1])
    _ _ h (morseFits_isoBeadsWord A 0).1 hu
  simpa only [List.append_assoc] using hf

/-- The ports of the orbit are a permutation of the ports. -/
private theorem sum_map_pairParkA {M : Type} [AddCommMonoid M] {r s : ℕ} (h : IsTorusPair r s)
    (hr : 3 ≤ r) (g : ℕ → M) :
    ((List.range r).map (fun k ↦ g (pairParkA r s k))).sum = ((List.range r).map g).sum := by
  have hp : ((List.range r).map (pairParkA r s)).Perm (List.range r) := by
    apply List.Subperm.perm_of_length_le
    · apply List.subperm_of_subset
      · exact List.Nodup.map_on (fun x hx y hy he ↦ pairParkA_inj h hr (List.mem_range.1 hx)
          (List.mem_range.1 hy) he) List.nodup_range
      · intro x hx
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
        exact List.mem_range.2 (Nat.mod_lt _ (by omega))
    · simp
  have := (hp.map g).sum_eq
  simpa [List.map_map, Function.comp_def] using this

/-- A sum over the ports split into the port `0`, the ports `1 … q - 1`, the ports `q`, `r - 1`. -/
private theorem sum_range_ports_inst {M : Type} [AddCommMonoid M] (r : ℕ) (hr : 3 ≤ r)
    (f : ℕ → M) :
    ((List.range r).map f).sum =
      f 0 + ((List.range (r - 3)).map (fun i ↦ f (i + 1))).sum + f (r - 2) + f (r - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 3 := ⟨r - 3, by omega⟩
  rw [show m + 3 = (m + 1) + 1 + 1 from rfl, List.sum_range_succ, List.sum_range_succ,
    List.sum_range_succ']
  simp only [show m + 1 + 1 + 1 - 3 = m by omega, show m + 1 + 1 + 1 - 2 = m + 1 by omega,
    show m + 1 + 1 + 1 - 1 = m + 1 + 1 by omega]

/-- `(c + a) mod r` vanishes for exactly one `a < r`. -/
private theorem sum_ite_mod_eq_zero_inst (r c : ℕ) (hr : 0 < r) :
    ((List.range r).map (fun a ↦ if (c + a) % r = 0 then 1 else 0)).sum = 1 := by
  have key : ∀ a < r, ((c + a) % r = 0 ↔ a = (r - c % r) % r) := by
    intro a ha
    have hc : c % r < r := Nat.mod_lt _ hr
    rw [Nat.add_mod, Nat.mod_eq_of_lt ha]
    have e1 : (c % r + a) % r = 0 ↔ c % r + a = 0 ∨ c % r + a = r := by
      rcases Nat.lt_or_ge (c % r + a) r with h1 | h1
      · rw [Nat.mod_eq_of_lt h1]; omega
      · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]; omega
    have e2 : (r - c % r) % r = if c % r = 0 then 0 else r - c % r := by
      split_ifs with h0
      · rw [h0, Nat.sub_zero, Nat.mod_self]
      · exact Nat.mod_eq_of_lt (by omega)
    rw [e1, e2]
    split_ifs <;> omega
  rw [List.map_congr_left (g := fun a ↦ if a = (r - c % r) % r then 1 else 0)
    (fun a ha ↦ if_congr (key a (List.mem_range.1 ha)) rfl rfl)]
  rw [← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  rw [Finset.sum_ite_eq']
  simp [Nat.mod_lt _ hr]

/-- The stack of a port other than `r - 1` is processable. -/
private theorem pairParkS1_procBeads (r s a : ℕ) (ha : a + 1 < r) :
    ∀ x ∈ pairParkS1 r s a, IsoProcBead x := by
  intro x hx
  simp only [pairParkS1] at hx
  split_ifs at hx with h0 h1 h2
  · simp only [List.mem_append, List.mem_singleton, List.mem_replicate, List.mem_flatten] at hx
    rcases hx with ((rfl | ⟨-, rfl⟩) | ⟨l, ⟨-, rfl⟩, hl⟩) | ⟨-, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr rfl))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inl rfl)
  · simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at hx
    rcases hx with rfl | ⟨-, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · simp only [List.nil_append, List.mem_replicate] at hx
    rw [hx.2]; exact Or.inr (Or.inl rfl)
  · omega

/-- The writhe of a concatenation. -/
private theorem isoBeadWr_append_inst (L M : List IsoBead) :
    isoBeadWr (L ++ M) = isoBeadWr L + isoBeadWr M := by
  simp only [isoBeadWr, List.count_append]; push_cast; ring

/-- The writhe of a `flatMap`. -/
private theorem isoBeadWr_flatMap_inst (f : ℕ → List IsoBead) :
    ∀ L : List ℕ, isoBeadWr (L.flatMap f) = (L.map (fun k ↦ isoBeadWr (f k))).sum
  | [] => by simp [isoBeadWr]
  | k :: L => by
    rw [List.flatMap_cons, isoBeadWr_append_inst, isoBeadWr_flatMap_inst f L, List.map_cons,
      List.sum_cons]

/-- The round curls: one per round. -/
private theorem sum_pairRho_inst (r s : ℕ) (hr : 0 < r) :
    ∀ m : ℕ, ((List.range r).map
      (fun a ↦ ((List.range m).filter (fun t ↦ (t + 2 + a) % r = 0)).length)).sum = m
  | 0 => by simp
  | m + 1 => by
    have ih := sum_pairRho_inst r s hr m
    have hu := sum_ite_mod_eq_zero_inst r (m + 2) hr
    simp only [List.range_succ, List.filter_append, List.length_append, List.filter_cons,
      List.filter_nil] at ih ⊢
    rw [List.sum_map_add, ih]
    congr 1
    rw [← hu]
    congr 1
    apply List.map_congr_left
    intro a _
    simp only [decide_eq_true_eq]
    split_ifs <;> simp_all

/-- The stacks of the port normal form, port by port. -/
private theorem pairParkS1_eval_inst (r s : ℕ) (hr : 3 ≤ r) :
    pairParkS1 r s 0 = [.t] ++ List.replicate (pairRunDown r s - 1) .lp ++
        (List.replicate (pairRunUp r s + 1) [IsoBead.t, .n]).flatten ++
        List.replicate (pairRho r s 0) .p ∧
      (∀ i, i + 1 < r - 2 → pairParkS1 r s (i + 1) = [.t] ++ List.replicate (pairRho r s (i + 1)) .p) ∧
      pairParkS1 r s (r - 2) = List.replicate (pairRho r s (r - 2)) .p ∧
      pairParkS1 r s (r - 1) = [.t, .cs] ++ List.replicate (pairRho r s (r - 1)) .p := by
  refine ⟨?_, fun i hi ↦ ?_, ?_, ?_⟩ <;> rw [pairParkS1] <;> split_ifs <;> first | omega | contradiction | rfl

/-- There are at least `r + 1` twists. -/
private theorem pairC_ge_inst {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) : r + 1 ≤ pairC r s := by
  have h1 := Nat.mul_le_mul_right s (show 2 ≤ r - 1 by omega)
  have h2 := h.2.1
  unfold pairC; omega

/-- The writhe of a twist block run. -/
private theorem isoBeadWr_blocks_inst (k : ℕ) :
    isoBeadWr (List.replicate k [IsoBead.t, .n]).flatten = -(k : ℤ) := by
  induction k with
  | zero => simp [isoBeadWr]
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, isoBeadWr_append_inst, ih]
    simp [isoBeadWr]

/-- The writhe of a run of curls. -/
private theorem isoBeadWr_replicate_inst (k : ℕ) (b : IsoBead) :
    isoBeadWr (List.replicate k b) = k * isoBeadWr [b] := by
  induction k with
  | zero => simp [isoBeadWr]
  | succ k ih =>
    rw [List.replicate_succ, show b :: List.replicate k b = [b] ++ List.replicate k b from rfl,
      isoBeadWr_append_inst, ih]
    push_cast; ring

/-- The beads before and after the clasp are processable. -/
theorem pairPark_procBeads {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    (∀ x ∈ pairParkLb r s, IsoProcBead x) ∧ ∀ x ∈ pairParkLa r s, IsoProcBead x := by
  obtain ⟨hK1, hKr, hKA, hKu⟩ := pairParkKs_spec h hr
  have hne : ∀ k < r, k ≠ pairParkKs r s → pairParkA r s k + 1 < r := by
    intro k hk hkK
    have h1 : pairParkA r s k < r := Nat.mod_lt _ (by omega)
    have h2 : pairParkA r s k ≠ r - 1 := fun he ↦ hkK (hKu k hk he)
    omega
  constructor
  · intro x hx
    simp only [pairParkLb, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with ((rfl | rfl) | ⟨k, hk, hx⟩) | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact pairParkS1_procBeads r s _ (hne k (by omega) (by omega)) x hx
    · exact Or.inl rfl
  · intro x hx
    simp only [pairParkLa, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_replicate,
      List.mem_singleton] at hx
    rcases hx with (⟨-, rfl⟩ | ⟨i, hi, hx⟩) | rfl
    · exact Or.inr (Or.inl rfl)
    · exact pairParkS1_procBeads r s _ (hne _ (by omega) (by omega)) x hx
    · exact Or.inr (Or.inl rfl)


/-- There are `C` twists. -/
theorem pairParkCount {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    isoBeadCountT (pairParkLb r s) + isoBeadCountT (pairParkLa r s) = pairC r s := by
  obtain ⟨e0, emid, eq, el⟩ := pairParkS1_eval_inst r s hr
  have hC := pairC_ge_inst h hr
  have e : isoBeadCountT (pairParkLb r s) + isoBeadCountT (pairParkLa r s) =
      isoBeadCountT (pairParkSigma r s) := by
    rw [pairParkSigma_split h hr]; simp [isoBeadCountT, List.count_append]
  rw [e]
  have hperm := sum_map_pairParkA (M := ℕ) h hr (fun a ↦ List.count IsoBead.t (pairParkS1 r s a))
  have hmid : ((List.range (r - 3)).map
      (fun i ↦ List.count IsoBead.t (pairParkS1 r s (i + 1)))).sum = r - 3 := by
    rw [List.map_congr_left (g := fun _ ↦ 1) (fun i hi ↦ by
      rw [emid i (by simp at hi; omega)]; simp [List.count_replicate])]
    simp
  simp only [pairParkSigma, isoBeadCountT, List.count_append, List.count_flatMap,
    Function.comp_def] at hperm ⊢
  rw [hperm, sum_range_ports_inst r hr, hmid, e0, eq, el]
  simp [List.count_replicate, List.count_flatten, pairRunUp]
  omega


/-- The curls have total writhe `0`. -/
theorem pairParkWr {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    isoBeadWr (pairParkLb r s) + isoBeadWr (pairParkLa r s) = 0 := by
  obtain ⟨e0, emid, eq, el⟩ := pairParkS1_eval_inst r s hr
  have hC := pairC_ge_inst h hr
  have e : isoBeadWr (pairParkLb r s) + isoBeadWr (pairParkLa r s) =
      isoBeadWr (pairParkSigma r s) := by
    rw [pairParkSigma_split h hr, isoBeadWr_append_inst, isoBeadWr_append_inst]
    simp [isoBeadWr]
  rw [e]
  have hperm := sum_map_pairParkA (M := ℤ) h hr (fun a ↦ isoBeadWr (pairParkS1 r s a))
  have hsplit : ∀ a ∈ List.range r, isoBeadWr (pairParkS1 r s a) =
      (if a = 0 then ((pairRunDown r s - 1 : ℕ) : ℤ) - ((pairRunUp r s + 1 : ℕ) : ℤ) else 0) +
        ((pairRho r s a : ℕ) : ℤ) := by
    intro a ha
    have ha' := List.mem_range.1 ha
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [e0]
      simp only [isoBeadWr_append_inst, isoBeadWr_blocks_inst, isoBeadWr_replicate_inst]
      simp [isoBeadWr]; ring
    · simp only [Nat.pos_iff_ne_zero.mp hpos, ↓reduceIte, zero_add]
      by_cases h1 : a < r - 2
      · obtain ⟨i, rfl⟩ : ∃ i, a = i + 1 := ⟨a - 1, by omega⟩
        rw [emid i h1]
        simp only [isoBeadWr_append_inst, isoBeadWr_replicate_inst]; simp [isoBeadWr]
      · by_cases h2 : a = r - 2
        · rw [h2, eq]
          simp only [isoBeadWr_replicate_inst]; simp [isoBeadWr]
        · rw [show a = r - 1 by omega, el]
          simp only [isoBeadWr_append_inst, isoBeadWr_replicate_inst]; simp [isoBeadWr]
  have hite : ((List.range r).map (fun a ↦
      (if a = 0 then ((pairRunDown r s - 1 : ℕ) : ℤ) - ((pairRunUp r s + 1 : ℕ) : ℤ) else 0))).sum =
      ((pairRunDown r s - 1 : ℕ) : ℤ) - ((pairRunUp r s + 1 : ℕ) : ℤ) := by
    rw [sum_range_ports_inst r hr]
    simp [show r - 2 ≠ 0 by omega, show r - 1 ≠ 0 by omega]
  have hrho : ((List.range r).map (fun a ↦ ((pairRho r s a : ℕ) : ℤ))).sum = ((s - 2 : ℕ) : ℤ) := by
    have := sum_pairRho_inst r s (by omega) (s - 2)
    rw [← this]
    push_cast [pairRho]
    simp [List.map_map, Function.comp_def]
  simp only [pairParkSigma, isoBeadWr_append_inst, isoBeadWr_flatMap_inst] at hperm ⊢
  rw [hperm, List.map_congr_left hsplit, List.sum_map_add, hite, hrho]
  have h2 := h.2.1
  have hE : pairRunDown r s - 1 = (r - 2) * (s - 1) := by simp [pairRunDown]
  simp only [isoBeadWr, hE, pairRunUp, pairC] at hC ⊢
  simp
  have a1 : r ≤ (r - 1) * s := by omega
  have a2 : 1 ≤ (r - 1) * s - r := by omega
  zify [a1, a2, show 2 ≤ r by omega, show 1 ≤ r by omega, show 1 ≤ s by omega,
    show 2 ≤ s by omega]
  ring


/-- The processing at the port `r - 1`. -/
theorem morseReach_pairParkW3_W4 {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    MorseReach 1 (pairParkW3 r s) (pairParkW4 r s) := by
  have hat : ∀ L : List IsoBead, pairParkAt r L = Function.update (fun _ ↦ []) (r - 1) L := by
    intro L; funext a
    by_cases ha : a = r - 1
    · subst ha; simp [pairParkAt]
    · simp [pairParkAt, ha]
  obtain ⟨hLb, hLa⟩ := pairPark_procBeads h hr
  have hp := morseReach_isoProc _ _ hLb hLa
  rw [pairParkCount h hr, show isoBeadWr (pairParkLb r s) - 2 * (isoBeadCountT (pairParkLa r s) : ℤ)
    = -pairParkWa r s by have := pairParkWr h hr; simp only [pairParkWa]; linarith] at hp
  rw [pairParkW3, pairParkW4, hat, hat, pairParkSigma_split h hr]
  exact morseReach_park_portLocal_inst r s (r - 1) [] [] _ _ _ hr (by omega) hp


end AJConjecture
