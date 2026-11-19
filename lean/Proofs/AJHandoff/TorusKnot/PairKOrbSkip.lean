import Mathlib
import AJHandoff.TorusKnot.PairKOrbDefs

/-!
# Descending products of a sequence with skipped residues

For a sequence `y : ℤ → G` all of whose windows of length `r` have the product `K`:

* `pairOrb_skip_prod`: `y (ρ + r w - 1) ⋯ y (ρ + 1)` without the terms `y (ρ + r k)` is
  `K ^ w * y ρ ^ (-w)` (each block `y (v + r - 1) ⋯ y (v + 1)` between two skipped terms is
  `K y_v⁻¹`, and `K y_v⁻¹ = y_(v+r)⁻¹ K`);
* `pairOrb_skip_frame`: if moreover `y` is `s`-periodic and `s + e = ρ + r w` with `e, ρ < r`, then
  `(y_(e-1) ⋯ y_0) · (y_(s-1) ⋯ y_0 without u ≡ ρ (mod r)) · (y_(ρ-1) ⋯ y_0)⁻¹ = K ^ w y_ρ^(-w)`.
  (Shift the first factor by `s`; no skipped index lies in `[s, s + e)` or in `[0, ρ)`.)

This is the algebra of the loops of the low strands (`AJHandoff.TorusKnot.PairKOrbPureLow`).
Checked exactly in the torus knot group for all `e, ρ < r` and
`(r, s) ∈ {(2,3), (2,5), (3,4), (3,5), (3,7), (4,5), (5,7), (4,9), (5,8), (7,9)}`.
Route: induction on `w` (split `List.range (r * (w + 1))` as `List.range (r * w)` plus `r` more
terms, `List.range_add`); for the frame lemma reindex with `List.range_add` and
`descProd_add`-style splitting, then apply `pairOrb_skip_prod` with `ρ`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-! ### Descending products -/

/-- The empty descending product. -/
private theorem descProd_zero_skp (g : ℕ → G) (a : ℕ) : descProd g a 0 = 1 := by
  simp [descProd]

/-- Splitting off the top factor of a descending product. -/
private theorem descProd_succ_top_skp (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = g (a + n) * descProd g a n := by
  simp [descProd, List.range_succ]

/-- Splitting off the bottom factor of a descending product. -/
private theorem descProd_succ_bot_skp (g : ℕ → G) (a n : ℕ) :
    descProd g a (n + 1) = descProd g (a + 1) n * g a := by
  induction n with
  | zero => simp [descProd]
  | succ n ih =>
    rw [descProd_succ_top_skp, ih, descProd_succ_top_skp, mul_assoc,
      show a + 1 + n = a + (n + 1) by omega]

/-- Descending products with the same factors agree. -/
private theorem descProd_congr_skp (g g' : ℕ → G) (a b n : ℕ)
    (H : ∀ i, i < n → g (a + i) = g' (b + i)) : descProd g a n = descProd g' b n := by
  induction n with
  | zero => simp [descProd_zero_skp]
  | succ n ih =>
    rw [descProd_succ_top_skp, descProd_succ_top_skp, H n (by omega),
      ih fun i hi ↦ H i (by omega)]

/-- Splitting off the bottom factor of a nonempty descending product from `0`. -/
private theorem descProd_split_bot_skp (g : ℕ → G) {n : ℕ} (hn : 1 ≤ n) :
    descProd g 0 n = descProd g 1 (n - 1) * g 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [descProd_succ_bot_skp, Nat.add_sub_cancel]

/-- A reversed range product is a descending product from `0`. -/
private theorem prod_range_reverse_skp (g : ℕ → G) (n : ℕ) :
    ((List.range n).reverse.map g).prod = descProd g 0 n := by
  simp only [descProd, Nat.zero_add]

/-- A reversed product over a shifted range. -/
private theorem prod_range_add_skp (g : ℕ → G) (a n : ℕ) :
    ((List.range (a + n)).reverse.map g).prod =
      descProd (fun i ↦ g (a + i)) 0 n * ((List.range a).reverse.map g).prod := by
  rw [List.range_add, List.reverse_append, List.map_append, List.prod_append, List.map_reverse,
    List.map_map, ← List.map_reverse, prod_range_reverse_skp]
  rfl

/-- The window relation, split at its bottom term: `y (p + r - 1) ⋯ y (p + 1) = K y_p⁻¹`. -/
private theorem window_top_skp {r : ℕ} (hr : 1 ≤ r) {K : G} {y : ℤ → G}
    (hw : ∀ p : ℤ, descProd (fun k ↦ y (p + k)) 0 r = K) (p : ℤ) :
    descProd (fun k ↦ y (p + k)) 1 (r - 1) = K * (y p)⁻¹ := by
  have w := hw p
  obtain ⟨n, hn⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [hn, descProd_succ_bot_skp, Nat.zero_add] at w
  rw [hn, Nat.add_sub_cancel, ← w]
  simp

/-- Conjugation by `K` shifts the sequence by `r`. -/
private theorem conj_skp {r : ℕ} (hr : 1 ≤ r) {K : G} {y : ℤ → G}
    (hw : ∀ p : ℤ, descProd (fun k ↦ y (p + k)) 0 r = K) (p : ℤ) :
    K * y p * K⁻¹ = y (p + r) := by
  have w1 := hw (p + 1)
  obtain ⟨n, hn⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [hn, descProd_succ_top_skp, Nat.zero_add] at w1
  have hM : descProd (fun k : ℕ ↦ y (p + 1 + k)) 0 n = K * (y p)⁻¹ := by
    rw [← window_top_skp hr hw p, hn, Nat.add_sub_cancel]
    exact descProd_congr_skp _ _ _ _ _ fun i _ ↦ by congr 1; push_cast; ring
  rw [hM] at w1
  have e : y (p + 1 + (n : ℤ)) = y (p + r) := by congr 1; rw [hn]; push_cast; ring
  rw [e] at w1
  calc K * y p * K⁻¹ = y (p + r) * (K * (y p)⁻¹) * (y p * K⁻¹) := by rw [w1]; group
    _ = y (p + r) := by group

/-- Conjugation by `K ^ n` shifts the sequence by `r n`. -/
private theorem conj_pow_skp {r : ℕ} (hr : 1 ≤ r) {K : G} {y : ℤ → G}
    (hw : ∀ p : ℤ, descProd (fun k ↦ y (p + k)) 0 r = K) (n : ℕ) (p : ℤ) :
    y (p + r * n) = K ^ n * y p * (K ^ n)⁻¹ := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [show p + (r : ℤ) * ((n + 1 : ℕ) : ℤ) = p + r * n + r by push_cast; ring,
      ← conj_skp hr hw, ih, pow_succ]
    group

/-- Adding `0 < k < r` changes the residue modulo `r`. -/
private theorem add_mod_ne_self_skp {a k r : ℕ} (hk : 0 < k) (hkr : k < r) :
    (a + k) % r ≠ a % r := by
  intro h
  have h' : a + k ≡ a + 0 [MOD r] := h
  have := Nat.ModEq.add_left_cancel' a h'
  unfold Nat.ModEq at this
  rw [Nat.mod_eq_of_lt hkr, Nat.zero_mod] at this
  omega

/-- Adding a nonzero residue changes the residue modulo `r`. -/
private theorem add_mod_ne_self_skp' {a k r : ℕ} (hk : k % r ≠ 0) :
    (a + k) % r ≠ a % r := by
  intro h
  have h' : a + k ≡ a + 0 [MOD r] := h
  have := Nat.ModEq.add_left_cancel' a h'
  unfold Nat.ModEq at this
  rw [Nat.zero_mod] at this
  exact hk this

/-- A descending product of a sequence with constant windows, skipping one residue class. -/
theorem pairOrb_skip_prod {r : ℕ} (hr : 1 ≤ r) (K : G) (y : ℤ → G)
    (hw : ∀ p : ℤ, descProd (fun k ↦ y (p + k)) 0 r = K) (ρ : ℤ) (w : ℕ) :
    ((List.range (r * w)).reverse.map fun k ↦ if k % r = 0 then 1 else y (ρ + k)).prod =
      K ^ w * y ρ ^ (-(w : ℤ)) := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [show r * (w + 1) = r * w + r by ring, prod_range_add_skp, ih]
    obtain ⟨n, hn⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
    have htop : descProd (fun i ↦ if (r * w + i) % r = 0 then 1 else y (ρ + ((r * w + i : ℕ) : ℤ)))
        0 r = K * (y (ρ + ((r * w : ℕ) : ℤ)))⁻¹ := by
      rw [← window_top_skp hr hw, descProd_split_bot_skp _ hr, Nat.add_zero, Nat.mul_mod_right,
        ite_eq_left rfl, mul_one]
      refine descProd_congr_skp _ _ _ _ _ fun i hi ↦ ?_
      have hne : (r * w + (1 + i)) % r ≠ 0 := by
        rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod,
          Nat.mod_eq_of_lt (by omega)]
        omega
      rw [ite_eq_right hne]
      congr 1
      push_cast
      ring
    rw [htop, show ρ + ((r * w : ℕ) : ℤ) = ρ + r * w by push_cast; ring, conj_pow_skp hr hw]
    push_cast
    group

/-- The rounds collected by a low strand, between the frames of its two ends. -/
theorem pairOrb_skip_frame {r s : ℕ} (hr : 1 ≤ r) (K : G) (y : ℤ → G)
    (hw : ∀ p : ℤ, descProd (fun k ↦ y (p + k)) 0 r = K) (hp : ∀ i : ℤ, y (i + s) = y i)
    {e ρ w : ℕ} (he : e < r) (hρ : ρ < r) (hs : s + e = ρ + r * w) :
    descProd (fun k ↦ y k) 0 e *
        ((List.range s).reverse.map fun u ↦ if u % r = ρ % r then 1 else y u).prod *
        (descProd (fun k ↦ y k) 0 ρ)⁻¹ = K ^ w * y ρ ^ (-(w : ℤ)) := by
  have hsplit := prod_range_add_skp (fun u : ℕ ↦ if u % r = ρ % r then 1 else y u) s e
  have hsplit' := prod_range_add_skp (fun u : ℕ ↦ if u % r = ρ % r then 1 else y u) ρ (r * w)
  rw [← hs] at hsplit'
  have htop : descProd (fun i ↦ (fun u : ℕ ↦ if u % r = ρ % r then 1 else y u) (s + i)) 0 e =
      descProd (fun k ↦ y k) 0 e := by
    refine descProd_congr_skp _ _ _ _ _ fun i hi ↦ ?_
    simp only [Nat.zero_add]
    rw [ite_eq_right ?_]
    · rw [Nat.cast_add, add_comm, hp]
    · intro hm
      have h1 : (s + i + (e - i)) % r = (s + i) % r := by
        rw [show s + i + (e - i) = ρ + r * w by omega, Nat.add_mul_mod_self_left, hm]
      exact add_mod_ne_self_skp (by omega) (by omega) h1
  have hmid : descProd (fun i ↦ (fun u : ℕ ↦ if u % r = ρ % r then 1 else y u) (ρ + i)) 0
      (r * w) = K ^ w * y ρ ^ (-(w : ℤ)) := by
    rw [← pairOrb_skip_prod hr K y hw ρ w, prod_range_reverse_skp]
    refine descProd_congr_skp _ _ _ _ _ fun i hi ↦ ?_
    simp only [Nat.zero_add]
    by_cases hi0 : i % r = 0
    · rw [ite_eq_left hi0, ite_eq_left]
      rw [Nat.add_mod, hi0, Nat.add_zero, Nat.mod_mod]
    · rw [ite_eq_right hi0, ite_eq_right, Nat.cast_add]
      intro hm
      exact add_mod_ne_self_skp' hi0 hm
  have hbot : ((List.range ρ).reverse.map fun u : ℕ ↦ if u % r = ρ % r then 1 else y u).prod =
      descProd (fun k ↦ y k) 0 ρ := by
    rw [prod_range_reverse_skp]
    refine descProd_congr_skp _ _ _ _ _ fun i hi ↦ ?_
    rw [ite_eq_right]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hρ]
    omega
  rw [htop] at hsplit
  rw [hmid, hbot] at hsplit'
  rw [← hsplit, hsplit']
  group

end AJConjecture
