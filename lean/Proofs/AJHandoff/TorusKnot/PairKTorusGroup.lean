import Mathlib
import AJConjecture.KnotGroup
import AJConjecture.MapLongitude
import AJFamily.Classical.BraidRunAppend
import AJFamily.Classical.BandWord
import AJFamily.Classical.FamilyPeripheralBlock
import AJHandoff.PairDefs

/-!
# The group of the torus knot `T(r, s)` in Artin's presentation

For `δ = σ_0 ⋯ σ_(r-2)`, Artin's action is `δ = inn(x_0) ∘ shift` (`x_j ↦ x_0 x_(j+1) x_0⁻¹`,
indices mod `r`), so `δ^r = inn(Π)` with `Π = x_0 x_1 ⋯ x_(r-1)`, and `Π` is fixed by `δ`. In
the knot group the relations say that `δ^s` acts trivially; hence `inn(Π^s) = δ^(rs) = id`:
`Π^s` is central (`torusFullProd_pow_comm`). The Artin longitude of the closure of `δ^s` is
`Π^s μ^(-rs)` (`longitude_torusPairKnot`; for `r = 2` this is `λ = c^(-m) (cd)^(2k+1)` of
`compLong`). Every generator is conjugate to the meridian (`exists_conj_meridian`, any knot).
-/

namespace AJConjecture

section TorusRun

variable {G : Type*} [Group G]

/-- The braid word `δ = σ_0 σ_1 ⋯ σ_(r-2)`. -/
private def torusPairDelta (r : ℕ) : BraidWord := (List.range (r - 1)).map fun i ↦ (i, true)

/-- The braid word `δ^n`. -/
private def torusPairDeltaPow (r n : ℕ) : BraidWord := (List.replicate n (torusPairDelta r)).flatten

/-- The entry of a tuple at an index read modulo `r`. -/
private def torusPairIdx {r : ℕ} (hr : 0 < r) (f : Fin r → G) (n : ℕ) : G :=
  f ⟨n % r, Nat.mod_lt _ hr⟩

omit [Group G] in
private theorem torusPairIdx_of_lt {r : ℕ} (hr : 0 < r) (f : Fin r → G) {n : ℕ} (hn : n < r) :
    torusPairIdx hr f n = f ⟨n, hn⟩ := by
  simp only [torusPairIdx, Nat.mod_eq_of_lt hn]

omit [Group G] in
private theorem torusPairIdx_mod {r : ℕ} (hr : 0 < r) (f : Fin r → G) (n : ℕ) :
    torusPairIdx hr f (n % r) = torusPairIdx hr f n := by
  simp only [torusPairIdx, Nat.mod_mod]

omit [Group G] in
private theorem torusPairIdx_add_self {r : ℕ} (hr : 0 < r) (f : Fin r → G) (n : ℕ) :
    torusPairIdx hr f (n + r) = torusPairIdx hr f n := by
  simp only [torusPairIdx, Nat.add_mod_right]

/-- The run of a word appended with one letter. -/
private theorem braidRun_append_singleton (m : ℕ) (w : BraidWord) (g : ℕ × Bool) (f : Fin m → G) :
    braidRun m (w ++ [g]) f = braidRunStep m (braidRun m w f) g := by
  simp only [braidRun, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A positive letter `σ_n` on a tuple, at the strand `n`. -/
private theorem braidRunStep_true_self {m n : ℕ} (h : n + 1 < m) (s : (Fin m → G) × (Fin m → G))
    (k : Fin m) (hk : (k : ℕ) = n) :
    (braidRunStep m s (n, true)).1 k = s.1 k * s.1 ⟨n + 1, h⟩ * (s.1 k)⁻¹ ∧
      (braidRunStep m s (n, true)).2 k = s.1 k * s.2 ⟨n + 1, h⟩ := by
  simp [braidRunStep, braidStep, artinGen, h, hk]

/-- A positive letter `σ_n` on a tuple, at the strand `n + 1`. -/
private theorem braidRunStep_true_succ {m n : ℕ} (h : n + 1 < m) (s : (Fin m → G) × (Fin m → G))
    (k : Fin m) (hk : (k : ℕ) = n + 1) :
    (braidRunStep m s (n, true)).1 k = s.1 ⟨n, by omega⟩ ∧
      (braidRunStep m s (n, true)).2 k = s.2 ⟨n, by omega⟩ := by
  simp [braidRunStep, braidStep, artinGen, h, hk]

/-- A positive letter `σ_n` on a tuple, away from its strands. -/
private theorem braidRunStep_true_ne {m n : ℕ} (s : (Fin m → G) × (Fin m → G)) (k : Fin m)
    (h1 : (k : ℕ) ≠ n) (h2 : (k : ℕ) ≠ n + 1) :
    (braidRunStep m s (n, true)).1 k = s.1 k ∧ (braidRunStep m s (n, true)).2 k = s.2 k := by
  by_cases h : n + 1 < m <;> simp [braidRunStep, braidStep, artinGen, h, h1, h2]

/-- The run of the prefix `σ_0 ⋯ σ_(n-1)` of `δ`. -/
private theorem braidRun_torusPairDelta_prefix {r : ℕ} (hr : 0 < r) (f : Fin r → G) (n : ℕ)
    (hn : n < r) :
    braidRun r ((List.range n).map fun i ↦ (i, true)) f =
      (fun k : Fin r ↦ if (k : ℕ) < n then
          torusPairIdx hr f 0 * torusPairIdx hr f (k + 1) * (torusPairIdx hr f 0)⁻¹
        else if (k : ℕ) = n then torusPairIdx hr f 0 else f k,
        fun k : Fin r ↦ if (k : ℕ) < n then torusPairIdx hr f 0 else 1) := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.map_nil, braidRun, List.foldl_nil, Nat.not_lt_zero,
      ite_false, Prod.mk.injEq, and_true]
    funext k
    split_ifs with hk
    · rw [torusPairIdx_of_lt hr f hr]
      congr 1
      exact Fin.ext hk
    · rfl
  | succ n ih =>
    have h : n + 1 < r := hn
    rw [List.range_succ, List.map_append, List.map_singleton, braidRun_append_singleton,
      ih (by omega)]
    refine Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)
    · by_cases h1 : (k : ℕ) = n
      · rw [(braidRunStep_true_self h _ k h1).1]
        simp only [h1, lt_irrefl, ite_false, ite_true, show n + 1 ≠ n by omega,
          show ¬ n + 1 < n by omega, show n < n + 1 by omega]
        rw [torusPairIdx_of_lt hr f h]
      · by_cases h2 : (k : ℕ) = n + 1
        · rw [(braidRunStep_true_succ h _ k h2).1]
          simp [h2]
        · rw [(braidRunStep_true_ne _ k h1 h2).1]
          by_cases h3 : (k : ℕ) < n
          · simp [h3, show (k : ℕ) < n + 1 by omega]
          · simp [h3, show ¬ (k : ℕ) < n + 1 by omega, h1, h2]
    · by_cases h1 : (k : ℕ) = n
      · rw [(braidRunStep_true_self h _ k h1).2]
        simp [h1]
      · by_cases h2 : (k : ℕ) = n + 1
        · rw [(braidRunStep_true_succ h _ k h2).2]
          simp [h2]
        · rw [(braidRunStep_true_ne _ k h1 h2).2]
          by_cases h3 : (k : ℕ) < n
          · simp [h3, show (k : ℕ) < n + 1 by omega]
          · simp [h3, show ¬ (k : ℕ) < n + 1 by omega]

/-- The run of `δ`: Artin's action is `inn(f_0) ∘ shift`, with conjugators `f_0` (and `1` at the
last strand). -/
private theorem braidRun_torusPairDelta {r : ℕ} (hr : 0 < r) (f : Fin r → G) :
    braidRun r (torusPairDelta r) f =
      (fun k : Fin r ↦
          torusPairIdx hr f 0 * torusPairIdx hr f (k + 1) * (torusPairIdx hr f 0)⁻¹,
        fun k : Fin r ↦ if (k : ℕ) + 1 < r then torusPairIdx hr f 0 else 1) := by
  rw [torusPairDelta, braidRun_torusPairDelta_prefix hr f (r - 1) (by omega)]
  refine Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)
  · have hk := k.isLt
    dsimp only
    split_ifs with h1 h2
    · rfl
    · rw [show (k : ℕ) + 1 = 0 + r by omega, torusPairIdx_add_self]
      group
    · omega
  · dsimp only
    congr 1
    exact propext (by omega)

/-- The strand map of `δ` is `k ↦ k + 1` modulo `r`. -/
private theorem artinWord_torusPairDelta_fst {r : ℕ} (hr : 0 < r) (k : Fin r) :
    (artinWord r (torusPairDelta r) k).1 = ⟨((k : ℕ) + 1) % r, Nat.mod_lt _ hr⟩ := by
  have h := braidRun_fst_apply r (torusPairDelta r) (FreeGroup.of : Fin r → FreeGroup (Fin r)) k
  rw [braidRun_torusPairDelta hr] at h
  dsimp only at h
  apply FreeGroup.of_injective
  change _ = torusPairIdx hr FreeGroup.of ((k : ℕ) + 1)
  split_ifs at h with h1
  · exact (mul_left_cancel (mul_right_cancel h)).symm
  · rw [one_mul, inv_one, mul_one] at h
    rw [← h, show (k : ℕ) + 1 = 0 + r by omega, torusPairIdx_add_self]
    group

/-- The run commutes with an endomorphism of the group of colours. -/
private theorem braidRun_comp_hom (m : ℕ) (w : BraidWord) (φ : G →* G) (f : Fin m → G) :
    braidRun m w (φ ∘ f) = (φ ∘ (braidRun m w f).1, φ ∘ (braidRun m w f).2) := by
  have hl : ∀ x, FreeGroup.lift (φ ∘ f) x = φ (FreeGroup.lift f x) := by
    intro x
    have : FreeGroup.lift (φ ∘ f) = φ.comp (FreeGroup.lift f) :=
      FreeGroup.ext_hom _ _ fun a ↦ by simp
    rw [this, MonoidHom.comp_apply]
  have h2 : ∀ k, (braidRun m w (φ ∘ f)).2 k = φ ((braidRun m w f).2 k) := by
    intro k
    rw [← lift_artinWord_snd, ← lift_artinWord_snd, hl]
  refine Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ h2 k)
  show (braidRun m w (φ ∘ f)).1 k = φ ((braidRun m w f).1 k)
  rw [braidRun_fst_apply, h2, braidRun_fst_apply m w f k]
  simp only [map_mul, map_inv, Function.comp_apply]

private theorem torusPairDeltaPow_add (r a b : ℕ) :
    torusPairDeltaPow r (a + b) = torusPairDeltaPow r a ++ torusPairDeltaPow r b := by
  simp only [torusPairDeltaPow, List.replicate_add, List.flatten_append]

private theorem torusPairDeltaPow_one (r : ℕ) : torusPairDeltaPow r 1 = torusPairDelta r := by
  simp [torusPairDeltaPow]

/-- The strand map of `δ^n` is `k ↦ k + n` modulo `r`. -/
private theorem artinWord_torusPairDeltaPow_fst {r : ℕ} (hr : 0 < r) (n : ℕ) (k : Fin r) :
    (artinWord r (torusPairDeltaPow r n) k).1 = ⟨((k : ℕ) + n) % r, Nat.mod_lt _ hr⟩ := by
  induction n generalizing k with
  | zero =>
    simp only [torusPairDeltaPow, List.replicate_zero, List.flatten_nil, artinWord,
      Nat.add_zero]
    exact Fin.ext (Nat.mod_eq_of_lt k.isLt).symm
  | succ n ih =>
    rw [torusPairDeltaPow_add, torusPairDeltaPow_one, artinWord_append_fst,
      artinWord_torusPairDelta_fst hr, ih]
    ext
    simp only [Nat.mod_add_mod]
    congr 1
    omega

/-- One more copy of `δ` on top. -/
private theorem braidRun_torusPairDeltaPow_succ {r : ℕ} (hr : 0 < r) (n : ℕ) (f : Fin r → G) :
    braidRun r (torusPairDeltaPow r (n + 1)) f =
      ((braidRun r (torusPairDelta r) (braidRun r (torusPairDeltaPow r n) f).1).1, fun i ↦
        (braidRun r (torusPairDelta r) (braidRun r (torusPairDeltaPow r n) f).1).2 i *
          (braidRun r (torusPairDeltaPow r n) f).2 ⟨((i : ℕ) + 1) % r, Nat.mod_lt _ hr⟩) := by
  rw [torusPairDeltaPow_add, torusPairDeltaPow_one, braidRun_append]
  simp only [artinWord_torusPairDelta_fst hr]

/-- The run of `δ^n` for `n ≤ r`, in terms of the chamber products `f_0 ⋯ f_(n-1)`. -/
private theorem braidRun_torusPairDeltaPow_of_le {r : ℕ} (hr : 0 < r) (f : Fin r → G) (n : ℕ)
    (hn : n ≤ r) :
    braidRun r (torusPairDeltaPow r n) f =
      (fun k : Fin r ↦ prePr f n * torusPairIdx hr f (k + n) * (prePr f n)⁻¹,
        fun k : Fin r ↦ if (k : ℕ) + n < r then prePr f n
          else prePr f n * (torusPairIdx hr f (k + n))⁻¹) := by
  induction n with
  | zero =>
    simp only [torusPairDeltaPow, List.replicate_zero, List.flatten_nil, braidRun,
      List.foldl_nil, prePr_zero, Nat.add_zero, one_mul, inv_one, mul_one]
    refine Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)
    · simp only [torusPairIdx, Nat.mod_eq_of_lt k.isLt]
    · simp [k.isLt]
  | succ n ih =>
    have hn' : n < r := by omega
    rw [braidRun_torusPairDeltaPow_succ hr, ih (by omega), braidRun_torusPairDelta hr,
      prePr_succ f n hn']
    have h0 : torusPairIdx hr f n = f ⟨n, hn'⟩ := torusPairIdx_of_lt hr f hn'
    have hT : ∀ j : ℕ, torusPairIdx hr
        (fun k : Fin r ↦ prePr f n * torusPairIdx hr f (k + n) * (prePr f n)⁻¹) j =
          prePr f n * torusPairIdx hr f (j + n) * (prePr f n)⁻¹ := by
      intro j
      simp only [torusPairIdx, Nat.mod_add_mod]
    refine Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)
    · dsimp only
      rw [hT, hT, Nat.zero_add, h0, show (k : ℕ) + 1 + n = k + (n + 1) by omega]
      group
    · dsimp only
      have hk := k.isLt
      rw [hT, Nat.zero_add, h0]
      by_cases h1 : (k : ℕ) + 1 < r
      · simp only [h1, ite_true, Nat.mod_eq_of_lt h1, show (k : ℕ) + 1 + n = k + (n + 1) by omega]
        split_ifs <;> group
      · have h2 : ((k : ℕ) + 1) % r = 0 := by
          rw [show (k : ℕ) + 1 = r by omega, Nat.mod_self]
        simp only [h1, ite_false, h2, Nat.zero_add, hn', ite_true,
          show (k : ℕ) + (n + 1) = n + r by omega, show ¬ n + r < r by omega,
          torusPairIdx_add_self, h0]
        group

/-- The run of `δ^r`: conjugation by `Π = f_0 ⋯ f_(r-1)`, with conjugators `Π f_k⁻¹`. -/
private theorem braidRun_torusPairDeltaPow_self {r : ℕ} (hr : 0 < r) (f : Fin r → G) :
    braidRun r (torusPairDeltaPow r r) f =
      (fun k : Fin r ↦ prePr f r * f k * (prePr f r)⁻¹,
        fun k : Fin r ↦ prePr f r * (f k)⁻¹) := by
  rw [braidRun_torusPairDeltaPow_of_le hr f r le_rfl]
  have hk : ∀ k : Fin r, torusPairIdx hr f (k + r) = f k := fun k ↦ by
    rw [torusPairIdx_add_self, torusPairIdx_of_lt hr f k.isLt]
  refine Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)
  · simp only [hk]
  · simp only [hk, show ¬ (k : ℕ) + r < r by omega, ite_false]

/-- The run of `δ^(rm)`: conjugation by `Π^m`, with conjugators `Π^m f_k^(-m)`. -/
private theorem braidRun_torusPairDeltaPow_mul {r : ℕ} (hr : 0 < r) (f : Fin r → G) (m : ℕ) :
    braidRun r (torusPairDeltaPow r (r * m)) f =
      (fun k : Fin r ↦ prePr f r ^ m * f k * (prePr f r ^ m)⁻¹,
        fun k : Fin r ↦ prePr f r ^ m * (f k ^ m)⁻¹) := by
  induction m with
  | zero =>
    simp only [Nat.mul_zero, torusPairDeltaPow, List.replicate_zero, List.flatten_nil, braidRun,
      List.foldl_nil, pow_zero, one_mul, inv_one, mul_one]
  | succ m ih =>
    have hc : (braidRun r (torusPairDeltaPow r (r * m)) f).1 =
        (MulAut.conj (prePr f r ^ m)).toMonoidHom ∘ f := by
      rw [ih]
      funext k
      simp only [MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    rw [Nat.mul_succ, torusPairDeltaPow_add, braidRun_append, hc, braidRun_comp_hom,
      braidRun_torusPairDeltaPow_self hr, ih]
    refine Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)
    · simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · simp only [Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        artinWord_torusPairDeltaPow_fst hr, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
      group

/-- If `f` is fixed by `δ^s`, the conjugators of `δ^(sn)` multiply along the orbit of the
strand map of `δ^s`. -/
private theorem braidRun_torusPairDeltaPow_mul_snd_of_fixed {r s : ℕ} (f : Fin r → G)
    (hfix : (braidRun r (torusPairDeltaPow r s) f).1 = f) (n : ℕ) :
    (braidRun r (torusPairDeltaPow r (s * n)) f).1 = f ∧
      ∀ i : Fin r, ((List.range n).map fun j ↦ (braidRun r (torusPairDeltaPow r s) f).2
        ((fun k ↦ (artinWord r (torusPairDeltaPow r s) k).1)^[j] i)).prod =
        (braidRun r (torusPairDeltaPow r (s * n)) f).2 i := by
  induction n with
  | zero =>
    simp [torusPairDeltaPow, braidRun]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Nat.mul_succ, torusPairDeltaPow_add, braidRun_append, ih1, hfix]
    refine ⟨rfl, fun i ↦ ?_⟩
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
    dsimp only
    rw [← ih2]
    simp only [Function.comp_def, Function.iterate_succ_apply, Function.iterate_zero_apply]

/-- If `f` is fixed by `δ^s`, then `Π^s` commutes with every entry of `f`. -/
private theorem prePr_pow_comm_of_fixed {r s : ℕ} (hr : 0 < r) (f : Fin r → G)
    (hfix : (braidRun r (torusPairDeltaPow r s) f).1 = f) (k : Fin r) :
    prePr f r ^ s * f k = f k * prePr f r ^ s := by
  have h1 := (braidRun_torusPairDeltaPow_mul_snd_of_fixed f hfix r).1
  rw [Nat.mul_comm, braidRun_torusPairDeltaPow_mul hr] at h1
  have h2 := congrFun h1 k
  dsimp only at h2
  rwa [mul_inv_eq_iff_eq_mul] at h2

private theorem writhe_torusPairDeltaPow (r n : ℕ) :
    writhe (torusPairDeltaPow r n) = ((n * (r - 1) : ℕ) : ℤ) := by
  induction n with
  | zero => simp [torusPairDeltaPow, writhe]
  | succ n ih =>
    rw [torusPairDeltaPow_add, torusPairDeltaPow_one]
    simp only [writhe, List.map_append, List.sum_append] at ih ⊢
    rw [ih]
    simp [torusPairDelta, Function.comp_def, Nat.succ_mul]

/-- If `f` is fixed by `δ^s`, the longitude product of the run of `δ^s` is `Π^s f_0^(-rs)`. -/
private theorem longitude_prod_of_fixed {r s : ℕ} (hr : 0 < r) (f : Fin r → G)
    (hfix : (braidRun r (torusPairDeltaPow r s) f).1 = f) :
    ((List.range r).map fun j ↦ (braidRun r (torusPairDeltaPow r s) f).2
        ((fun k ↦ (artinWord r (torusPairDeltaPow r s) k).1)^[j] ⟨0, hr⟩)).prod *
      f ⟨0, hr⟩ ^ (-writhe (torusPairDeltaPow r s)) =
      prePr f r ^ s * f ⟨0, hr⟩ ^ (-((r * s : ℕ) : ℤ)) := by
  rw [(braidRun_torusPairDeltaPow_mul_snd_of_fixed f hfix r).2, Nat.mul_comm,
    braidRun_torusPairDeltaPow_mul hr, writhe_torusPairDeltaPow]
  dsimp only
  rw [mul_assoc, ← zpow_natCast (f ⟨0, hr⟩) s, ← zpow_neg, ← zpow_add]
  congr 2
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

end TorusRun

/-- The strand map of Artin's action is the strand permutation of the word. -/
private theorem artinWord_fst_eq_strandPerm (m : ℕ) (w : BraidWord) (k : Fin m) :
    (artinWord m w k).1 = strandPerm m w k := by
  induction w with
  | nil => simp [artinWord, strandPerm]
  | cons g w ih =>
    rw [strandPerm, List.map_cons, List.prod_cons, ← strandPerm, Equiv.Perm.mul_apply, ← ih]
    simp only [artinWord]
    generalize (artinWord m w k).1 = l
    by_cases h : g.1 + 1 < m
    · simp only [artinGen, strandSwap, h, dite_true, Equiv.swap_apply_def]
      split_ifs <;> simp only [Fin.ext_iff] at * <;> omega
    · simp [artinGen, strandSwap, h]

/-- Each Artin generator is conjugate in the knot group to the generator of its image strand. -/
private theorem knotGroup_of_eq_conj (K : BraidKnot) (k : Fin K.strands) :
    (PresentedGroup.of k : KnotGroup K) =
      PresentedGroup.mk _ (artinWord K.strands K.word k).2 *
        PresentedGroup.of (strandPerm K.strands K.word k) *
        (PresentedGroup.mk _ (artinWord K.strands K.word k).2)⁻¹ := by
  have hmem : (FreeGroup.of k)⁻¹ *
      ((artinWord K.strands K.word k).2 * FreeGroup.of (artinWord K.strands K.word k).1 *
        ((artinWord K.strands K.word k).2)⁻¹) ∈ artinRels K := ⟨k, rfl⟩
  have h := PresentedGroup.one_of_mem hmem
  rw [map_mul, map_inv, inv_mul_eq_one, map_mul, map_mul, map_inv] at h
  rw [← artinWord_fst_eq_strandPerm]
  exact h



/-- The product `Π = x_0 x_1 ⋯ x_(r-1)` of the Artin generators of `T(r, s)`. -/
def torusFullProd {r s : ℕ} (h : IsTorusPair r s) : KnotGroup (torusPairKnot r s h) :=
  ((List.finRange r).map fun j ↦ (PresentedGroup.of j : KnotGroup (torusPairKnot r s h))).prod

/-- `Π` is the chamber product of all the generators. -/
private theorem torusFullProd_eq_prePr {r s : ℕ} (h : IsTorusPair r s) :
    torusFullProd h =
      prePr (fun k : Fin r ↦ (PresentedGroup.of k : KnotGroup (torusPairKnot r s h))) r := by
  unfold prePr torusFullProd
  rw [List.ofFn_eq_map, List.take_of_length_le (by simp)]
  rfl

/-- `Π^s` is central in the group of `T(r, s)`. -/
theorem torusFullProd_pow_comm {r s : ℕ} (h : IsTorusPair r s)
    (x : KnotGroup (torusPairKnot r s h)) :
    torusFullProd h ^ s * x = x * torusFullProd h ^ s := by
  have hr : 0 < r := by obtain ⟨hr, -⟩ := h; omega
  have hfix : (braidRun r (torusPairDeltaPow r s)
      (fun k : Fin r ↦ (PresentedGroup.of k : KnotGroup (torusPairKnot r s h)))).1 =
      fun k ↦ PresentedGroup.of k :=
    braidRun_fst_of_hom (torusPairKnot r s h) (MonoidHom.id _)
  have hmem : x ∈ Subgroup.centralizer {torusFullProd h ^ s} := by
    refine PresentedGroup.generated_by _ _ (fun j ↦ ?_) x
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rw [torusFullProd_eq_prePr]
    exact prePr_pow_comm_of_fixed hr _ hfix j
  rw [Subgroup.mem_centralizer_iff] at hmem
  exact hmem _ rfl

/-- The preferred longitude of `T(r, s)` is `Π^s μ^(-rs)`. -/
theorem longitude_torusPairKnot {r s : ℕ} (h : IsTorusPair r s) :
    longitude (torusPairKnot r s h) =
      torusFullProd h ^ s * meridian (torusPairKnot r s h) ^ (-((r * s : ℕ) : ℤ)) := by
  have hr : 0 < r := by obtain ⟨hr, -⟩ := h; omega
  have hfix : (braidRun r (torusPairDeltaPow r s)
      (fun k : Fin r ↦ (PresentedGroup.of k : KnotGroup (torusPairKnot r s h)))).1 =
      fun k ↦ PresentedGroup.of k :=
    braidRun_fst_of_hom (torusPairKnot r s h) (MonoidHom.id _)
  have hL := map_longitude (torusPairKnot r s h) (MonoidHom.id _)
  simp only [MonoidHom.id_apply] at hL
  rw [hL, torusFullProd_eq_prePr]
  exact longitude_prod_of_fixed hr _ hfix

/-- In the group of a knot every Artin generator is a conjugate of the meridian. -/
theorem exists_conj_meridian (K : BraidKnot) (j : Fin K.strands) :
    ∃ g : KnotGroup K, (PresentedGroup.of j : KnotGroup K) = g * meridian K * g⁻¹ := by
  have hn : ∀ n : ℕ, ∃ g : KnotGroup K, meridian K =
      g * PresentedGroup.of ((strandPerm K.strands K.word ^ n) ⟨0, K.strands_pos⟩) * g⁻¹ := by
    intro n
    induction n with
    | zero => exact ⟨1, by simp [meridian]⟩
    | succ n ih =>
      obtain ⟨g, hg⟩ := ih
      refine ⟨g * PresentedGroup.mk _
        (artinWord K.strands K.word ((strandPerm K.strands K.word ^ n) ⟨0, K.strands_pos⟩)).2,
        ?_⟩
      rw [hg, knotGroup_of_eq_conj K, pow_succ', Equiv.Perm.mul_apply]
      group
  obtain ⟨n, hn'⟩ := K.connected ⟨0, K.strands_pos⟩ j
  obtain ⟨g, hg⟩ := hn n
  rw [hn'] at hg
  exact ⟨g⁻¹, by rw [hg]; group⟩

/-- Artin's action of `δ^n = (σ_0 ⋯ σ_(r-2))^n` on a tuple: conjugation of the tuple shifted by
`n` by the cyclic product `f_0 f_1 ⋯ f_(n-1)` (indices modulo `r`). -/
theorem braidRun_torusPairWord_fst {G : Type*} [Group G] {r : ℕ} (hr : 0 < r) (n : ℕ)
    (f : Fin r → G) (k : Fin r) :
    (braidRun r (torusPairWord r n) f).1 k =
      ((List.range n).map fun t ↦ f ⟨t % r, Nat.mod_lt _ hr⟩).prod *
        f ⟨((k : ℕ) + n) % r, Nat.mod_lt _ hr⟩ *
        ((List.range n).map fun t ↦ f ⟨t % r, Nat.mod_lt _ hr⟩).prod⁻¹ := by
  change (braidRun r (torusPairDeltaPow r n) f).1 k = _
  induction n generalizing k with
  | zero =>
    simp only [torusPairDeltaPow, List.replicate_zero, List.flatten_nil, braidRun,
      List.foldl_nil, List.range_zero, List.map_nil, List.prod_nil, one_mul, inv_one, mul_one,
      Nat.add_zero]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt k.isLt).symm
  | succ n ih =>
    rw [braidRun_torusPairDeltaPow_succ hr, braidRun_torusPairDelta hr]
    dsimp only
    simp only [torusPairIdx, ih, List.range_succ, List.map_append, List.map_singleton,
      List.prod_append, List.prod_singleton, Nat.zero_mod, Nat.zero_add, Nat.mod_add_mod]
    simp only [show (k : ℕ) + 1 + n = k + (n + 1) by omega]
    group

end AJConjecture
