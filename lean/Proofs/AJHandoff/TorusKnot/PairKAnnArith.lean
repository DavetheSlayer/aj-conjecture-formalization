import Mathlib
import AJHandoff.TorusKnot.PairKAnnDefs

/-!
# The label arithmetic of the annulus path

The chain index `i(t)` (`pairAnnIdx`) is the unique `i < r` with `r ∣ t + i s` (`r, s` coprime),
and the height is `h(t) = (t + i(t) s) / r`. The identities used by the transition lemmas:

* `pairAnn_chain`: a round step `t ↦ t + r` keeps the chain index and raises the height by one;
* `pairAnn_bottom`: the bottom connection `T_(s+1+k) → T_(k+1)` (`k < r - 2`): the index drops by
  one (`s + 1 + k + (i - 1)s = k + 1 + i s`), the height is kept, and the chain of `k + 1` is not
  the chain `i(r - 1)` that follows the run, so `l` drops by one;
* `pairAnn_run`: the run connection `T_(s-1) → T_(r-1)`: `i(s - 1) = i(r - 1) - 1`, the height
  grows by one and `l` drops by `z + 3`;
* `pairAnn_ends`: `i(0) = i(r) = 0`, `i(s) = r - 1`, hence `h(0) = 0`, `h(r) = 1`, `h(s) = s`,
  `l(0) = 0`, `l(r) = -1` and `l(s) = -(s + r + z) = 1 - rs` (as `z = c - r - 1`);
* `pairAnn_congr`: `(h(t) - h(1)) r = t - 1 + (i(t) - i(1)) s ≡ t - 1 (mod s)`.

Route: `pairAnnIdx_spec` from `List.find?` (a solution exists: `s` is invertible mod `r`,
`Nat.Coprime`), `pairAnnIdx_unique` from `r ∣ (i - i')s` and coprimality; every other statement is
uniqueness plus `omega`/`Nat.div` arithmetic (`pairAnnHt_mul`). All statements are checked by
`pairAnnCheckLab` (`#guard` in `AJHandoff.TorusKnot.PairKAnnDefs`).
-/

namespace AJConjecture

variable {r s : ℕ}

/-- The chain index is a solution of `r ∣ t + i s` below `r`. -/
theorem pairAnnIdx_spec (h : IsTorusPair r s) (t : ℕ) :
    pairAnnIdx r s t < r ∧ (t + pairAnnIdx r s t * s) % r = 0 := by
  obtain ⟨hr, hrs, hcop⟩ := h
  have : NeZero r := ⟨by omega⟩
  have hex : ∃ i ∈ List.range r, ((t + i * s) % r == 0) = true := by
    refine ⟨((-(t : ZMod r)) * (s : ZMod r)⁻¹).val, List.mem_range.2 (ZMod.val_lt _), ?_⟩
    rw [beq_iff_eq]
    apply Nat.mod_eq_zero_of_dvd
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_assoc, mul_comm _ (s : ZMod r),
      ZMod.coe_mul_inv_eq_one s hcop.symm]
    ring
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 (List.find?_isSome.2 hex)
  have h1 := List.find?_some hj
  have h2 := List.mem_of_find?_eq_some hj
  rw [pairAnnIdx, hj, Option.getD_some]
  exact ⟨List.mem_range.1 h2, by simpa using h1⟩

/-- The chain index is the only solution below `r`. -/
theorem pairAnnIdx_unique (h : IsTorusPair r s) {t i : ℕ} (hi : i < r)
    (ht : (t + i * s) % r = 0) : pairAnnIdx r s t = i := by
  obtain ⟨hj, hjt⟩ := pairAnnIdx_spec h t
  have hm : pairAnnIdx r s t * s ≡ i * s [MOD r] :=
    Nat.ModEq.add_left_cancel' t (hjt.trans ht.symm)
  have := Nat.ModEq.cancel_right_of_coprime h.2.2 hm
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hi] at this

/-- `h(t) r = t + i(t) s`. -/
theorem pairAnnHt_mul (h : IsTorusPair r s) (t : ℕ) :
    pairAnnHt r s t * r = t + pairAnnIdx r s t * s :=
  Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (pairAnnIdx_spec h t).2)

/-- A round step `t ↦ t + r` keeps the chain index and raises the height by one. -/
theorem pairAnn_chain (h : IsTorusPair r s) (t : ℕ) :
    pairAnnIdx r s (t + r) = pairAnnIdx r s t ∧ pairAnnHt r s (t + r) = pairAnnHt r s t + 1 := by
  have hr : 0 < r := by have := h.1; omega
  have hi := pairAnnIdx_spec h t
  have h1 : pairAnnIdx r s (t + r) = pairAnnIdx r s t :=
    pairAnnIdx_unique h hi.1 (by
      rw [show t + r + pairAnnIdx r s t * s = t + pairAnnIdx r s t * s + r by ring,
        Nat.add_mod_right]
      exact hi.2)
  refine ⟨h1, Nat.eq_of_mul_eq_mul_right hr ?_⟩
  rw [pairAnnHt_mul h, h1, Nat.add_mul, one_mul, pairAnnHt_mul h]
  ring

/-- The bottom connection `T_(s+1+k) → T_(k+1)`. -/
theorem pairAnn_bottom (h : IsTorusPair r s) (k : ℕ) (hk : k < r - 2) :
    pairAnnHt r s (s + 1 + k) = pairAnnHt r s (k + 1) ∧
      pairAnnTopL r s (s + 1 + k) = pairAnnTopL r s (k + 1) + 1 := by
  obtain ⟨hr, hrs, hcop⟩ := id h
  have hi := pairAnnIdx_spec h (k + 1)
  have hiR := pairAnnIdx_spec h (r - 1)
  obtain ⟨i, hieq⟩ : ∃ i, pairAnnIdx r s (k + 1) = i := ⟨_, rfl⟩
  rw [hieq] at hi
  have hi0 : i ≠ 0 := by
    intro h0
    have := hi.2
    rw [h0, zero_mul, add_zero, Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hshift : s + 1 + k + (i - 1) * s = k + 1 + i * s := by
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have h1 : pairAnnIdx r s (s + 1 + k) = i - 1 :=
    pairAnnIdx_unique h (by omega) (by rw [hshift]; exact hi.2)
  have hh : pairAnnHt r s (s + 1 + k) = pairAnnHt r s (k + 1) :=
    Nat.eq_of_mul_eq_mul_right (by omega : 0 < r) (by
      rw [pairAnnHt_mul h, pairAnnHt_mul h, h1, hshift, hieq])
  have hne : i ≠ pairAnnIdx r s (r - 1) := by
    intro he
    rw [← he] at hiR
    have hm : k + 1 + i * s ≡ r - 1 + i * s [MOD r] := hi.2.trans hiR.2.symm
    have := Nat.ModEq.add_right_cancel' _ hm
    rw [Nat.ModEq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  refine ⟨hh, ?_⟩
  simp only [pairAnnTopL, h1, hh, hieq]
  split_ifs <;> omega

/-- The run connection `T_(s-1) → T_(r-1)`. -/
theorem pairAnn_run (h : IsTorusPair r s) :
    pairAnnHt r s (r - 1) = pairAnnHt r s (s - 1) + 1 ∧
      pairAnnTopL r s (r - 1) = pairAnnTopL r s (s - 1) - pairRunUp r s - 3 := by
  obtain ⟨hr, hrs, hcop⟩ := id h
  have hiR := pairAnnIdx_spec h (r - 1)
  obtain ⟨i, hieq⟩ : ∃ i, pairAnnIdx r s (r - 1) = i := ⟨_, rfl⟩
  rw [hieq] at hiR
  have hi0 : i ≠ 0 := by
    intro h0
    have := hiR.2
    rw [h0, zero_mul, add_zero, Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hshift : s - 1 + (i - 1) * s + r = r - 1 + i * s := by
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.add_mul, one_mul]
    generalize i' * s = m
    omega
  have h1 : pairAnnIdx r s (s - 1) = i - 1 :=
    pairAnnIdx_unique h (by omega) (by
      have := hiR.2
      rwa [← hshift, Nat.add_mod_right] at this)
  have hh : pairAnnHt r s (r - 1) = pairAnnHt r s (s - 1) + 1 :=
    Nat.eq_of_mul_eq_mul_right (by omega : 0 < r) (by
      rw [pairAnnHt_mul h, Nat.add_mul, one_mul, pairAnnHt_mul h, h1, hieq, ← hshift])
  refine ⟨hh, ?_⟩
  simp only [pairAnnTopL, h1, hh, hieq]
  split_ifs <;> omega

/-- The labels at `T_0`, `T_r` and `T_s`. -/
theorem pairAnn_ends (h : IsTorusPair r s) :
    pairAnnHt r s 0 = 0 ∧ pairAnnTopL r s 0 = 0 ∧ pairAnnHt r s r = 1 ∧
      pairAnnTopL r s r = -1 ∧ pairAnnHt r s s = s ∧
      pairAnnTopL r s s + ((r * s : ℕ) : ℤ) = 1 := by
  obtain ⟨hr, hrs, hcop⟩ := id h
  obtain ⟨-, -, hc, -⟩ := pairGap_arithRv h
  have hiR := pairAnnIdx_spec h (r - 1)
  have hiR0 : pairAnnIdx r s (r - 1) ≠ 0 := by
    intro h0
    have := hiR.2
    rw [h0, zero_mul, add_zero, Nat.mod_eq_of_lt (by omega)] at this
    omega
  have i0 : pairAnnIdx r s 0 = 0 := pairAnnIdx_unique h (by omega) (by simp)
  have ir : pairAnnIdx r s r = 0 := pairAnnIdx_unique h (by omega) (by simp)
  have hrs' : r * s = s + (r - 1) * s := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have is : pairAnnIdx r s s = r - 1 :=
    pairAnnIdx_unique h (by omega) (by rw [← hrs', Nat.mul_mod_right])
  have h0 : pairAnnHt r s 0 = 0 := by simp [pairAnnHt, i0]
  have hr1 : pairAnnHt r s r = 1 := by simp [pairAnnHt, ir, Nat.div_self (by omega : 0 < r)]
  have hss : pairAnnHt r s s = s := by
    rw [pairAnnHt, is, ← hrs', Nat.mul_div_cancel_left _ (by omega)]
  have hc' : pairC r s + s = r * s := by
    unfold pairC
    rw [hrs']
    ring
  refine ⟨h0, ?_, hr1, ?_, hss, ?_⟩
  · simp only [pairAnnTopL, h0, i0]
    split_ifs <;> omega
  · simp only [pairAnnTopL, hr1, ir]
    split_ifs <;> omega
  · simp only [pairAnnTopL, hss, is, pairRunUp]
    have := hiR.1
    split_ifs <;> omega

/-- The congruence of the `Π`-exponents: `(h(t) - h(1)) r ≡ t - 1 (mod s)`. -/
theorem pairAnn_congr (h : IsTorusPair r s) (t : ℕ) :
    (pairAnnTopW r s t - pairAnnTopW r s 1) * r ≡ (t : ℤ) - 1 [ZMOD s] := by
  rw [Int.modEq_iff_dvd]
  have h1 : ((pairAnnHt r s t : ℕ) : ℤ) * r = t + (pairAnnIdx r s t : ℤ) * s := by
    exact_mod_cast pairAnnHt_mul h t
  have h2 : ((pairAnnHt r s 1 : ℕ) : ℤ) * r = 1 + (pairAnnIdx r s 1 : ℤ) * s := by
    exact_mod_cast pairAnnHt_mul h 1
  refine ⟨(pairAnnIdx r s 1 : ℤ) - pairAnnIdx r s t, ?_⟩
  simp only [pairAnnTopW]
  linear_combination (-1 : ℤ) * h1 + h2

end AJConjecture
