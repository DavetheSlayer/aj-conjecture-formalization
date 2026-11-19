import Mathlib
import AJHandoff.TorusKnot.PairKAnnDefs

/-!
# The Hurwitz sequence of a torus tuple

For a tuple `y` with cyclic products `P(n) = y_0 ⋯ y_(n-1)` (indices mod `r`, `pairRevCyc`),
`Π = P(r)` (`pairAnnPi`) and `R'_p = P(p + 1) P(p)⁻¹` (`pairAnnHur`):

* algebra (no relation): `P(k) = y_0 ⋯ y_(k-1)` for `k ≤ r` (`pairRevCyc_eq_asc`),
  `Π = (y_0 ⋯ y_(r-2)) y_(r-1)`, `R'_k = P(k) y_k P(k)⁻¹` for `k < r`, the rounds of the rotated
  tuple `R_t = y_(r-1) R'_(t-1) y_(r-1)⁻¹` for `t ≥ 1` (`pairRevPu_succ_eq`), and
  `R'_(p+r) = Π R'_p Π⁻¹` (`P(r + n) = Π P(n)`);
* under the torus relation `y_k = P(s) y_((k+s) mod r) P(s)⁻¹`: `P(p + s) = P(p) P(s)`, hence
  `R'_(p+s) = R'_p`; `y_(r-1) = R'_(s-1)` (from `P(s) = y_(r-1) P(s-1)`, `pairRevPu_torus`);
  `R_(s-1) = y_(r-2)` (`pairRevPu_climb` with `k = 1`); `R'_(s-2) = y_(r-1)⁻¹ y_(r-2) y_(r-1)`
  (`R'_(s-2) = Π⁻¹ R'_(r-2) Π`); `Π^s = P(rs) = P(s)^r` commutes with `y_0 = R'_0`
  (`R'_(rs) = Π^s R'_0 Π^(-s)` and `R'_(rs) = R'_0`); and finally
  `R'_p = Π^w y_0 Π^(-w)` whenever `w r ≡ p (mod s)`, `w ∈ ℤ` (reduce `w` modulo `s` with the
  central `Π^s`, then iterate the two shift rules).

Checked exactly in the free product of the torus knot group with `ℤ` (`SCR/ANN/validate.py`,
checks `HB*`, `HT*`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-! ### Algebra -/

/-- `P(k) = y_0 ⋯ y_(k-1)` for `k ≤ r`. -/
theorem pairRevCyc_eq_asc (r : ℕ) (y : ℕ → G) (k : ℕ) (hk : k ≤ r) :
    pairRevCyc r y k = pairRevAsc y 0 k := by
  refine congrArg List.prod (List.map_congr_left fun t ht ↦ ?_)
  rw [Nat.zero_add, Nat.mod_eq_of_lt (by have := List.mem_range.1 ht; omega)]

/-- `Π = (y_0 ⋯ y_(r-2)) y_(r-1)`. -/
theorem pairAnnPi_eq {r : ℕ} (hr : 1 ≤ r) (y : ℕ → G) :
    pairAnnPi r y = pairRevAsc y 0 (r - 1) * y (r - 1) := by
  rw [pairAnnPi, pairRevCyc_eq_asc r y r le_rfl]
  conv_lhs => rw [show r = r - 1 + 1 by omega]
  rw [pairRevAsc_succ, Nat.zero_add]

/-- `Λ = Π^s y_0^(-rs)`. -/
theorem pairRevLam_eq (r s : ℕ) (y : ℕ → G) :
    pairRevLam r s y = pairAnnPi r y ^ s * y 0 ^ (-((r * s : ℕ) : ℤ)) := by
  rw [pairRevLam, pairAnnPi, pairRevCyc]
  congr 3
  exact List.map_congr_left fun t ht ↦ by rw [Nat.mod_eq_of_lt (List.mem_range.1 ht)]

/-- `R'_k = P(k) y_k P(k)⁻¹` for `k < r`. -/
theorem pairAnnHur_lt (r : ℕ) (y : ℕ → G) (k : ℕ) (hk : k < r) :
    pairAnnHur r y k = pairRevAsc y 0 k * y k * (pairRevAsc y 0 k)⁻¹ := by
  rw [pairAnnHur, pairRevCyc_eq_asc r y (k + 1) (by omega), pairRevCyc_eq_asc r y k (by omega),
    pairRevAsc_succ, Nat.zero_add]

/-- The rounds of the rotated tuple: `R_t = y_(r-1) R'_(t-1) y_(r-1)⁻¹` for `t ≥ 1`. -/
theorem pairRevRound_eq_hur {r : ℕ} (hr : 1 ≤ r) (y : ℕ → G) (t : ℕ) (ht : 1 ≤ t) :
    pairRevRound r y t = y (r - 1) * pairAnnHur r y (t - 1) * (y (r - 1))⁻¹ := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  rw [pairRevRound, pairRevPu_succ_eq hr, pairRevPu_succ_eq hr, pairAnnHur, Nat.add_sub_cancel]
  group

/-- `P(r + n) = Π P(n)`. -/
theorem pairRevCyc_add_r (r : ℕ) (y : ℕ → G) (n : ℕ) :
    pairRevCyc r y (r + n) = pairAnnPi r y * pairRevCyc r y n := by
  rw [pairRevCyc, List.range_add, List.map_append, List.prod_append, List.map_map]
  congr 1
  refine congrArg List.prod (List.map_congr_left fun i _ ↦ ?_)
  simp only [Function.comp_apply, Nat.add_mod_left]

/-- `R'_(p+r) = Π R'_p Π⁻¹`. -/
theorem pairAnnHur_add_r (r : ℕ) (y : ℕ → G) (p : ℕ) :
    pairAnnHur r y (p + r) = pairAnnPi r y * pairAnnHur r y p * (pairAnnPi r y)⁻¹ := by
  rw [pairAnnHur, pairAnnHur, show p + r + 1 = r + (p + 1) by omega, show p + r = r + p by omega,
    pairRevCyc_add_r, pairRevCyc_add_r]
  group

/-- `R'_(p + r n) = Π^n R'_p Π^(-n)`. -/
theorem pairAnnHur_add_mul_r (r : ℕ) (y : ℕ → G) (p n : ℕ) :
    pairAnnHur r y (p + r * n) = pairAnnPi r y ^ n * pairAnnHur r y p * (pairAnnPi r y ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show p + r * (n + 1) = p + r * n + r by ring, pairAnnHur_add_r, ih, pow_succ']
    group

/-! ### Under the torus relation -/

section Torus

variable {r s : ℕ}

/-- `R'` is `s`-periodic. -/
theorem pairAnnHur_add_s (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (p : ℕ) : pairAnnHur r y (p + s) = pairAnnHur r y p := by
  have hr := h.1
  -- `P(s + n) = P(n) P(s)`
  have hP : ∀ n, pairRevCyc r y (s + n) = pairRevCyc r y n * pairRevCyc r y s := by
    intro n
    induction n with
    | zero => simp [pairRevCyc]
    | succ n ih =>
      have hk := hy (n % r) (Nat.mod_lt _ (by omega))
      rw [show (n % r + s) % r = (s + n) % r by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_comm]] at hk
      rw [← Nat.add_assoc, pairRevCyc_succ, ih, pairRevCyc_succ, hk]
      group
  rw [pairAnnHur, pairAnnHur, show p + s + 1 = s + (p + 1) by omega, show p + s = s + p by omega,
    hP, hP]
  group

/-- `R'_(p + s n) = R'_p`. -/
theorem pairAnnHur_add_mul_s (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (p n : ℕ) : pairAnnHur r y (p + s * n) = pairAnnHur r y p := by
  induction n with
  | zero => simp
  | succ n ih => rw [show p + s * (n + 1) = p + s * n + s by ring, pairAnnHur_add_s h y hy, ih]

/-- `y_(r-1) = R'_(s-1)`. -/
theorem pairAnn_y_last (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹) :
    y (r - 1) = pairAnnHur r y (s - 1) := by
  obtain ⟨hr, hrs, -⟩ := h
  obtain ⟨hP, -⟩ := pairRevPu_torus (by omega) (by omega) y hy
  have h1 : pairRevCyc r y s = y (r - 1) * pairRevCyc r y (s - 1) := by
    rw [← hP, show s = s - 1 + 1 by omega, pairRevPu_succ_eq (by omega), Nat.add_sub_cancel]
  rw [pairAnnHur, show s - 1 + 1 = s by omega, h1]
  group

/-- The last round is `R_(s-1) = y_(r-2)`. -/
theorem pairRevRound_last (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹) :
    pairRevRound r y (s - 1) = y (r - 2) := by
  obtain ⟨hr, hrs, -⟩ := h
  rw [pairRevRound, show s - 1 + 1 = s by omega,
    pairRevPu_climb (by omega) (by omega) y hy 1 (by omega) (by omega)]
  simp only [pairRevAsc, List.range_one, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, Nat.add_zero]
  congr 1
  rw [show r - 1 + r - 1 = r - 2 + r by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- `R'_(s-2) = y_(r-1)⁻¹ y_(r-2) y_(r-1)`. -/
theorem pairAnnHur_s_two (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹) :
    pairAnnHur r y (s - 2) = (y (r - 1))⁻¹ * y (r - 2) * y (r - 1) := by
  obtain ⟨hr, hrs, -⟩ := id h
  have h1 := pairAnnHur_add_r r y (s - 2)
  rw [show s - 2 + r = r - 2 + s by omega, pairAnnHur_add_s h y hy,
    pairAnnHur_lt r y (r - 2) (by omega), pairAnnPi_eq (by omega)] at h1
  have hasc : pairRevAsc y 0 (r - 1) = pairRevAsc y 0 (r - 2) * y (r - 2) := by
    rw [show r - 1 = r - 2 + 1 by omega, pairRevAsc_succ, Nat.zero_add]
  rw [hasc] at h1
  -- `h1 : Q y Q⁻¹ = (Q y z) R'(s-2) (Q y z)⁻¹`; solve for `R'(s-2)`
  calc pairAnnHur r y (s - 2)
      = (pairRevAsc y 0 (r - 2) * y (r - 2) * y (r - 1))⁻¹ *
          (pairRevAsc y 0 (r - 2) * y (r - 2) * y (r - 1) * pairAnnHur r y (s - 2) *
            (pairRevAsc y 0 (r - 2) * y (r - 2) * y (r - 1))⁻¹) *
          (pairRevAsc y 0 (r - 2) * y (r - 2) * y (r - 1)) := by group
    _ = (y (r - 1))⁻¹ * y (r - 2) * y (r - 1) := by rw [← h1]; group

/-- `Π^s` commutes with `y_0`. -/
theorem pairAnnPi_zpow_comm (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹) :
    pairAnnPi r y ^ (s : ℤ) * y 0 = y 0 * pairAnnPi r y ^ (s : ℤ) := by
  have hr := h.1
  have h0 : pairAnnHur r y 0 = y 0 := by
    rw [pairAnnHur_lt r y 0 (by omega)]; simp [pairRevAsc]
  have h1 := pairAnnHur_add_mul_r r y 0 s
  rw [show 0 + r * s = 0 + s * r by ring, pairAnnHur_add_mul_s h y hy, h0] at h1
  rw [zpow_natCast]
  calc pairAnnPi r y ^ s * y 0
      = pairAnnPi r y ^ s * y 0 * (pairAnnPi r y ^ s)⁻¹ * pairAnnPi r y ^ s := by group
    _ = y 0 * pairAnnPi r y ^ s := by rw [← h1]

/-- `R'_p = Π^w y_0 Π^(-w)` whenever `w r ≡ p (mod s)`. -/
theorem pairAnnHur_eq_conj (h : IsTorusPair r s) (y : ℕ → G)
    (hy : ∀ k, k < r → y k = pairRevCyc r y s * y ((k + s) % r) * (pairRevCyc r y s)⁻¹)
    (w : ℤ) (p : ℕ) (hw : w * r ≡ p [ZMOD s]) :
    pairAnnHur r y p = pairAnnPi r y ^ w * y 0 * (pairAnnPi r y ^ w)⁻¹ := by
  obtain ⟨hr, hrs, -⟩ := id h
  have hs0 : (s : ℤ) ≠ 0 := by omega
  -- reduce `w` modulo `s`: `Π^s` commutes with `y_0`
  set w' : ℕ := (w % s).toNat with hw'
  have hw'z : (w' : ℤ) = w % s := Int.toNat_of_nonneg (Int.emod_nonneg _ hs0)
  have hsplit : w = w' + s * (w / s) := by rw [hw'z]; exact (Int.emod_add_mul_ediv w s).symm
  have hc : Commute (pairAnnPi r y ^ ((s : ℤ) * (w / s))) (y 0) := by
    rw [zpow_mul]
    exact (Commute.zpow_left (pairAnnPi_zpow_comm h y hy) _)
  have hconj : pairAnnPi r y ^ w * y 0 * (pairAnnPi r y ^ w)⁻¹ =
      pairAnnPi r y ^ w' * y 0 * (pairAnnPi r y ^ w')⁻¹ := by
    rw [hsplit, zpow_add, zpow_natCast, mul_assoc (pairAnnPi r y ^ w'), hc.eq]
    group
  -- `R'_p = R'_(p mod s) = R'_(w' r mod s) = R'_(w' r) = Π^(w') y_0 Π^(-w')`
  have hmod : (w' * r) % s = p % s := by
    have h1 : ((w' : ℤ) * r) % s = (p : ℤ) % s := by
      rw [hw'z, Int.mul_emod, Int.emod_emod_of_dvd w (dvd_refl _), ← Int.mul_emod]
      exact hw.eq
    exact_mod_cast h1
  have h0 : pairAnnHur r y 0 = y 0 := by
    rw [pairAnnHur_lt r y 0 (by omega)]; simp [pairRevAsc]
  have hp1 : pairAnnHur r y p = pairAnnHur r y (p % s) := by
    conv_lhs => rw [← Nat.mod_add_div p s]
    exact pairAnnHur_add_mul_s h y hy _ _
  have hp2 : pairAnnHur r y (w' * r) = pairAnnHur r y ((w' * r) % s) := by
    conv_lhs => rw [← Nat.mod_add_div (w' * r) s]
    exact pairAnnHur_add_mul_s h y hy _ _
  have hp3 := pairAnnHur_add_mul_r r y 0 w'
  rw [Nat.zero_add, h0, Nat.mul_comm r w'] at hp3
  rw [hconj, hp1, ← hmod, ← hp2, hp3]

end Torus

end AJConjecture
