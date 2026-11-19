import Mathlib
import AJHandoff.TorusKnot.PairKIsoParkDefs

/-!
# Stage C by ports: the orbit of the ports along the knot

`pairParkA r s k = (q + k s) mod r` is the port of the `k`-th conveyor pass of the knot. For a
torus pair (`gcd(r, s) = 1`, `3 ≤ r < s`):

* `pairParkA_inj`: the ports `a_0, …, a_{r-1}` are distinct (a permutation of `0 … r - 1`);
* `pairParkA_succ`: `a_{k+1} = (a_k + s) mod r`, `a_0 = q`, and `a_k ≠ q` for `1 ≤ k < r`
  (the knot meets the top end only after the last pass, `a_r = q`);
* `pairParkKs_spec`: `K* ∈ [1, r - 1]` is the unique pass index with `a_{K*} = r - 1`
  (the pass that starts after the right arc, i.e. after the clasp).

Pure arithmetic (`Nat.Coprime`, `Nat.ModEq`).
-/

namespace AJConjecture

set_option linter.unusedVariables false in
/-- The ports of the passes are distinct. -/
theorem pairParkA_inj {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) {k k' : ℕ} (hk : k < r)
    (hk' : k' < r) (he : pairParkA r s k = pairParkA r s k') : k = k' := by
  have hc : Nat.gcd r s = 1 := h.2.2
  have h1 : r - 2 + k * s ≡ r - 2 + k' * s [MOD r] := he
  have h2 := Nat.ModEq.cancel_right_of_coprime hc (Nat.ModEq.add_left_cancel' _ h1)
  have h3 : k % r = k' % r := h2
  rwa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at h3

/-- The next port along the knot; the first and the last pass. -/
theorem pairParkA_succ {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) (k : ℕ) :
    pairParkA r s (k + 1) = (pairParkA r s k + s) % r ∧ pairParkA r s 0 = r - 2 ∧
      pairParkA r s r = r - 2 ∧ (1 ≤ k → k < r → pairParkA r s k ≠ r - 2) ∧
      pairParkA r s k < r ∧ (pairParkA r s k + s) % r ≠ pairParkA r s k := by
  have hr0 : 0 < r := by omega
  refine ⟨?_, ?_, ?_, ?_, Nat.mod_lt _ hr0, ?_⟩
  · simp only [pairParkA]
    rw [Nat.mod_add_mod]
    congr 1
    ring
  · simp only [pairParkA, zero_mul, Nat.add_zero]; exact Nat.mod_eq_of_lt (by omega)
  · simp only [pairParkA, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
  · intro hk1 hkr he
    have h0 : pairParkA r s 0 = r - 2 := by
      simp only [pairParkA, zero_mul, Nat.add_zero]; exact Nat.mod_eq_of_lt (by omega)
    have := pairParkA_inj h hr hkr (by omega : 0 < r) (he.trans h0.symm)
    omega
  · intro he
    have hlt : pairParkA r s k < r := Nat.mod_lt _ hr0
    have h1 : (pairParkA r s k + s) % r = (pairParkA r s k + 0) % r := by
      rw [Nat.add_zero, Nat.mod_eq_of_lt hlt]; exact he
    have h2 : s % r = 0 % r := Nat.ModEq.add_left_cancel' _ h1
    have hd : r ∣ s := Nat.dvd_of_mod_eq_zero (by simpa using h2)
    have hc : Nat.gcd r s = 1 := h.2.2
    rw [Nat.gcd_eq_left hd] at hc
    omega

/-- The pass after the right arc. -/
theorem pairParkKs_spec {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) :
    1 ≤ pairParkKs r s ∧ pairParkKs r s < r ∧ pairParkA r s (pairParkKs r s) = r - 1 ∧
      ∀ k < r, pairParkA r s k = r - 1 → k = pairParkKs r s := by
  have hr0 : 0 < r := by omega
  have hsub : (Finset.range r).image (pairParkA r s) ⊆ Finset.range r := fun x hx ↦ by
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (Nat.mod_lt _ hr0)
  have hcard : (Finset.range r).card ≤ ((Finset.range r).image (pairParkA r s)).card := by
    rw [Finset.card_image_of_injOn fun a ha b hb he ↦
      pairParkA_inj h hr (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) he]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  obtain ⟨k₀, hk₀, hA₀⟩ : ∃ k₀ < r, pairParkA r s k₀ = r - 1 := by
    have : r - 1 ∈ (Finset.range r).image (pairParkA r s) := by
      rw [heq]; exact Finset.mem_range.2 (by omega)
    obtain ⟨k, hk, he⟩ := Finset.mem_image.1 this
    exact ⟨k, Finset.mem_range.1 hk, he⟩
  have hne : (List.range r).filter (fun k ↦ pairParkA r s k = r - 1) ≠ [] := by
    intro hnil
    have : k₀ ∈ (List.range r).filter (fun k ↦ pairParkA r s k = r - 1) :=
      List.mem_filter.2 ⟨List.mem_range.2 hk₀, by simpa using hA₀⟩
    rw [hnil] at this
    simp at this
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
  have hKs : pairParkKs r s = x := by simp [pairParkKs, hx]
  have hxm : x ∈ (List.range r).filter (fun k ↦ pairParkA r s k = r - 1) := by
    rw [hx]; exact List.mem_cons_self
  rw [List.mem_filter, List.mem_range] at hxm
  have hAx : pairParkA r s x = r - 1 := by simpa using hxm.2
  have h0 : pairParkA r s 0 = r - 2 := by
    simp only [pairParkA, zero_mul, Nat.add_zero]; exact Nat.mod_eq_of_lt (by omega)
  rw [hKs]
  refine ⟨?_, hxm.1, hAx, fun k hk hAk ↦ pairParkA_inj h hr hk hxm.1 (hAk.trans hAx.symm)⟩
  rcases Nat.eq_zero_or_pos x with rfl | hpos
  · rw [h0] at hAx; omega
  · exact hpos

end AJConjecture
