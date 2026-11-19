import Mathlib
import AJTwist.Knot.TwKBlocks
import AJHandoff.TorusKnot.PairKConnected

/-!
# The closure of the twisted word is connected

The strand permutation of a block word is the product of the transpositions of its blocks.
Replacing a transposition `(a b)` by the product of the transpositions along a path
`a, p₁, …, p_k, b` through fresh points turns every orbit through `a` into the same orbit with the
excursion `p₁, …, p_k` inserted (`exists_pow_of_swap_path`). The chain `twChain` is such a path
from the disc `0` to the disc `twHeadTop r s` through all the new discs, so the connectedness of
`twWhiteheadWord r s ℓ σ` follows from `connected_pairWhiteheadWord` (the Hopf letters of either
sign give the same transposition).
-/

namespace AJConjecture

/-- Rerouting `(a b)` through one fresh point `p`: one step of `swap a b * R` outside `S` and
`p` is one or two steps of `swap a p * (swap p b * R)`. -/
private theorem exists_pow_reroute_step_twKConnected {α : Type*} [DecidableEq α]
    (R : Equiv.Perm α) (a b p : α) (S : List α) (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b)
    (hpa : p ≠ a) (hpb : p ≠ b) (hRp : R p = p) (hRS : ∀ q ∈ S, R q = q) {x : α} (hxS : x ∉ S)
    (hxp : x ≠ p) :
    ((Equiv.swap a b * R) x ∉ S ∧ (Equiv.swap a b * R) x ≠ p) ∧
      ∃ m : ℕ, ((Equiv.swap a p * (Equiv.swap p b * R)) ^ m) x = (Equiv.swap a b * R) x := by
  have hRxS : R x ∉ S := fun hmem ↦ hxS (R.injective (hRS _ hmem) ▸ hmem)
  have hRxp : R x ≠ p := fun he ↦ hxp (R.injective (he.trans hRp.symm))
  by_cases h1 : R x = a
  · have hσ : (Equiv.swap a b * R) x = b := by
      rw [Equiv.Perm.mul_apply, h1, Equiv.swap_apply_left]
    refine ⟨by rw [hσ]; exact ⟨hb, hpb.symm⟩, 2, ?_⟩
    rw [hσ, pow_two, Equiv.Perm.mul_apply]
    simp only [Equiv.Perm.mul_apply, h1]
    rw [Equiv.swap_apply_of_ne_of_ne hpa.symm hab, Equiv.swap_apply_left, hRp,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hab.symm hpb.symm]
  · by_cases h2 : R x = b
    · have hσ : (Equiv.swap a b * R) x = a := by
        rw [Equiv.Perm.mul_apply, h2, Equiv.swap_apply_right]
      refine ⟨by rw [hσ]; exact ⟨ha, hpa.symm⟩, 1, ?_⟩
      rw [hσ, pow_one]
      simp only [Equiv.Perm.mul_apply, h2]
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · have hσ : (Equiv.swap a b * R) x = R x := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
      refine ⟨by rw [hσ]; exact ⟨hRxS, hRxp⟩, 1, ?_⟩
      rw [hσ, pow_one]
      simp only [Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hRxp h2, Equiv.swap_apply_of_ne_of_ne h1 hRxp]

/-- Rerouting `(a b)` through one fresh point `p`: every point of the orbit of `a` under
`swap a b * R` lies outside `S`, is not `p`, and lies on the orbit of `a` under
`swap a p * (swap p b * R)`. -/
private theorem exists_pow_reroute_orbit_twKConnected {α : Type*} [DecidableEq α]
    (R : Equiv.Perm α) (a b p : α) (S : List α) (ha : a ∉ S) (hb : b ∉ S) (hab : a ≠ b)
    (hpa : p ≠ a) (hpb : p ≠ b) (hRp : R p = p) (hRS : ∀ q ∈ S, R q = q) (n : ℕ) :
    (((Equiv.swap a b * R) ^ n) a ∉ S ∧ ((Equiv.swap a b * R) ^ n) a ≠ p) ∧
      ∃ m : ℕ, ((Equiv.swap a p * (Equiv.swap p b * R)) ^ m) a = ((Equiv.swap a b * R) ^ n) a := by
  induction n with
  | zero => exact ⟨⟨ha, hpa.symm⟩, 0, rfl⟩
  | succ n ih =>
    obtain ⟨⟨h1, h2⟩, m, hm⟩ := ih
    obtain ⟨h3, m', hm'⟩ :=
      exists_pow_reroute_step_twKConnected R a b p S ha hb hab hpa hpb hRp hRS h1 h2
    rw [pow_succ', Equiv.Perm.mul_apply]
    refine ⟨h3, m' + m, ?_⟩
    rw [pow_add, Equiv.Perm.mul_apply, hm, hm']

/-- The pointwise form of `exists_pow_of_swap_path`: a point outside the path that is reached
from `a` by `swap a b * R` is reached by the rerouted permutation, and so is every point of the
path as soon as `R⁻¹ a` is reached by `swap a b * R`. -/
private theorem exists_pow_swap_path_pointwise_twKConnected {α : Type*} [DecidableEq α] (a : α)
    (path : List α) : ∀ (R : Equiv.Perm α) (b : α), path.Nodup → a ∉ path → b ∉ path → a ≠ b →
    (∀ p ∈ path, R p = p) →
    (∀ x, x ∉ path → (∃ n : ℕ, ((Equiv.swap a b * R) ^ n) a = x) →
      ∃ n : ℕ, (((List.zipWith Equiv.swap (a :: path) (path ++ [b])).prod * R) ^ n) a = x) ∧
    (∀ x ∈ path, (∃ n : ℕ, ((Equiv.swap a b * R) ^ n) a = R⁻¹ a) →
      ∃ n : ℕ, (((List.zipWith Equiv.swap (a :: path) (path ++ [b])).prod * R) ^ n) a = x) := by
  induction path using List.reverseRecOn with
  | nil =>
    intro R b _ _ _ _ _
    refine ⟨fun x _ hx ↦ ?_, fun x hx ↦ absurd hx List.not_mem_nil⟩
    simpa using hx
  | append_singleton path p ih =>
    intro R b hnd ha hb hab hR
    rw [List.nodup_append] at hnd
    obtain ⟨hnd, -, hp⟩ := hnd
    have hpS : p ∉ path := fun hmem ↦ hp p hmem p (List.mem_singleton_self p) rfl
    rw [List.mem_append, List.mem_singleton, not_or] at ha hb
    have hRp : R p = p := hR p (by simp)
    have hRS : ∀ q ∈ path, R q = q := fun q hq ↦ hR q (by simp [hq])
    have hpa : p ≠ a := Ne.symm ha.2
    have hpb : p ≠ b := Ne.symm hb.2
    have hprod : (List.zipWith Equiv.swap (a :: (path ++ [p])) (path ++ [p] ++ [b])).prod * R =
        (List.zipWith Equiv.swap (a :: path) (path ++ [p])).prod * (Equiv.swap p b * R) := by
      rw [← List.cons_append, List.zipWith_append (by simp), List.prod_append]
      simp [mul_assoc]
    have hR' : ∀ q ∈ path, (Equiv.swap p b * R) q = q := fun q hq ↦ by
      rw [Equiv.Perm.mul_apply, hRS q hq, Equiv.swap_apply_of_ne_of_ne]
      · exact fun h ↦ hpS (h ▸ hq)
      · exact fun h ↦ hb.1 (h ▸ hq)
    have hinv : (Equiv.swap p b * R)⁻¹ a = R⁻¹ a := by
      rw [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hpa.symm hab]
    obtain ⟨ih1, ih2⟩ := ih (Equiv.swap p b * R) p hnd ha.1 hpS ha.2 hR'
    rw [hprod]
    have horb := exists_pow_reroute_orbit_twKConnected R a b p path ha.1 hb.1 hab hpa hpb hRp hRS
    have hfirst : ∀ x, (∃ n : ℕ, ((Equiv.swap a b * R) ^ n) a = x) →
        x ∉ path ∧ ∃ m : ℕ, ((Equiv.swap a p * (Equiv.swap p b * R)) ^ m) a = x := by
      rintro x ⟨n, rfl⟩
      exact ⟨(horb n).1.1, (horb n).2⟩
    refine ⟨fun x _ hx ↦ ih1 x (hfirst x hx).1 (hfirst x hx).2, fun x hx hreach ↦ ?_⟩
    obtain ⟨hnot, m, hm⟩ := hfirst _ hreach
    rcases List.mem_append.1 hx with hx | hx
    · exact ih2 x hx ⟨m, by rw [hinv]; exact hm⟩
    · rw [List.mem_singleton] at hx
      subst hx
      refine ih1 x hpS ⟨m + 1, ?_⟩
      rw [pow_succ', Equiv.Perm.mul_apply, hm]
      simp only [Equiv.Perm.mul_apply]
      rw [show R (R⁻¹ a) = a from R.apply_symm_apply a,
        Equiv.swap_apply_of_ne_of_ne hpa.symm hab, Equiv.swap_apply_left]

/-- Rerouting a transposition through fresh points keeps a permutation transitive: if `R` fixes
the points of the path, and every point outside the path is reached from `a` by `swap a b * R`,
then every point is reached from `a` by the product of the swaps along `a, p₁, …, p_k, b`
followed by `R`. -/
theorem exists_pow_of_swap_path {α : Type*} [DecidableEq α] (R : Equiv.Perm α) (a b : α)
    (path : List α) (hnd : path.Nodup) (ha : a ∉ path) (hb : b ∉ path) (hab : a ≠ b)
    (hR : ∀ p ∈ path, R p = p)
    (h : ∀ x, x ∉ path → ∃ n : ℕ, ((Equiv.swap a b * R) ^ n) a = x) (x : α) :
    ∃ n : ℕ, (((List.zipWith Equiv.swap (a :: path) (path ++ [b])).prod * R) ^ n) a = x := by
  obtain ⟨h1, h2⟩ := exists_pow_swap_path_pointwise_twKConnected a path R b hnd ha hb hab hR
  by_cases hx : x ∈ path
  · refine h2 x hx (h _ fun hmem ↦ ha ?_)
    have := hR _ hmem
    rw [show R (R⁻¹ a) = a from R.apply_symm_apply a] at this
    rwa [← this] at hmem
  · exact h1 x hx (h x hx)

/-- The transposition of the positions of a block. -/
private def blockSwapTwKConnected : SBlock → Equiv.Perm ℕ
  | .band i j => Equiv.swap i j
  | .neg i => Equiv.swap i (i + 1)

/-- The permutation of the positions of a list of blocks. -/
private def blocksPermTwKConnected (bs : List SBlock) : Equiv.Perm ℕ :=
  (bs.map blockSwapTwKConnected).prod

/-- The transposition of a block is its strand map. -/
private theorem blockSwapTwKConnected_apply (b : SBlock) (t : ℕ) :
    blockSwapTwKConnected b t = b.perm t := by
  cases b <;> simp only [blockSwapTwKConnected, SBlock.perm, Equiv.swap_apply_def]

/-- The permutation of a list of blocks is its strand map. -/
private theorem blocksPermTwKConnected_apply (bs : List SBlock) (t : ℕ) :
    blocksPermTwKConnected bs t = stPerm bs t := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [blocksPermTwKConnected, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply,
      ← blocksPermTwKConnected, ih, blockSwapTwKConnected_apply, stPerm]

/-- The permutation of a concatenation of block lists. -/
private theorem blocksPermTwKConnected_append (bs cs : List SBlock) :
    blocksPermTwKConnected (bs ++ cs) = blocksPermTwKConnected bs * blocksPermTwKConnected cs := by
  simp only [blocksPermTwKConnected, List.map_append, List.prod_append]

/-- The sign of the Hopf letters does not change the permutation. -/
private theorem blocksPermTwKConnected_map_clasp (σ : Bool) (bs : List SBlock) :
    blocksPermTwKConnected (bs.map (twClaspBlock σ)) = blocksPermTwKConnected bs := by
  rw [blocksPermTwKConnected, List.map_map, blocksPermTwKConnected]
  refine congrArg List.prod (List.map_congr_left fun b _ ↦ ?_)
  cases b <;> cases σ <;> rfl

/-- Blocks on `M` strands fix the positions from `M` on. -/
private theorem blocksPermTwKConnected_of_le {M : ℕ} (bs : List SBlock)
    (hv : ∀ b ∈ bs, b.Valid M) {t : ℕ} (ht : M ≤ t) : blocksPermTwKConnected bs t = t := by
  rw [blocksPermTwKConnected_apply]
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hv
    rw [stPerm, ih hv.2]
    obtain ⟨hb, -⟩ := hv
    cases b <;> simp only [SBlock.Valid, SBlock.perm] at hb ⊢ <;> split_ifs <;> omega

/-- The strand map of Artin's action is the strand permutation of the word. -/
private theorem artinWord_fst_eq_strandPerm_twKConnected (m : ℕ) (w : BraidWord) (k : Fin m) :
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

/-- The powers of the strand permutation of a block word, on the positions. -/
private theorem strandPerm_pow_val_twKConnected {m : ℕ} (bs : List SBlock)
    (hv : ∀ b ∈ bs, b.Valid m) (n : ℕ) (x : Fin m) :
    (((strandPerm m (blocksWord bs) ^ n) x : Fin m) : ℕ) = (blocksPermTwKConnected bs ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      ← artinWord_fst_eq_strandPerm_twKConnected, artinWord_blocksWord_fst _ hv, ih,
      blocksPermTwKConnected_apply]

/-- Consecutive pairs of a run `g 0, …, g k`. -/
private theorem zipWith_map_range_twKConnected {α β : Type*} (f : α → α → β) (g : ℕ → α)
    (k : ℕ) : ∀ X Y : List α,
    List.zipWith f ((List.range (k + 1)).map g ++ X)
        ((List.range k).map (fun i ↦ g (i + 1)) ++ Y) =
      (List.range k).map (fun i ↦ f (g i) (g (i + 1))) ++ List.zipWith f (g k :: X) Y := by
  induction k with
  | zero => intro X Y; simp
  | succ k ih =>
    intro X Y
    have e0 : (List.range (k + 1 + 1)).map g = (List.range (k + 1)).map g ++ [g (k + 1)] := by
      rw [List.range_succ, List.map_append, List.map_singleton]
    have e1 : (List.range (k + 1)).map (fun i ↦ g (i + 1)) =
        (List.range k).map (fun i ↦ g (i + 1)) ++ [g (k + 1)] := by
      rw [List.range_succ, List.map_append, List.map_singleton]
    have e2 : (List.range (k + 1)).map (fun i ↦ f (g i) (g (i + 1))) =
        (List.range k).map (fun i ↦ f (g i) (g (i + 1))) ++ [f (g k) (g (k + 1))] := by
      rw [List.range_succ, List.map_append, List.map_singleton]
    rw [e0, e1, e2, List.append_assoc, List.append_assoc, ih, List.append_assoc]
    rfl

/-- The first element of a run. -/
private theorem map_range_succ_twKConnected {α : Type*} (g : ℕ → α) (k : ℕ) :
    (List.range (k + 1)).map g = g 0 :: (List.range k).map (fun i ↦ g (i + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-- The consecutive pairs of a path made of two runs. -/
private theorem zipWith_two_runs_twKConnected {α β : Type*} (f : α → α → β) (a b : α)
    (g₁ g₂ : ℕ → α) (k₁ k₂ : ℕ) :
    List.zipWith f (a :: ((List.range (k₁ + 1)).map g₁ ++ (List.range (k₂ + 1)).map g₂))
        ((List.range (k₁ + 1)).map g₁ ++ (List.range (k₂ + 1)).map g₂ ++ [b]) =
      [f a (g₁ 0)] ++ (List.range k₁).map (fun i ↦ f (g₁ i) (g₁ (i + 1))) ++
        [f (g₁ k₁) (g₂ 0)] ++ (List.range k₂).map (fun i ↦ f (g₂ i) (g₂ (i + 1))) ++
        [f (g₂ k₂) b] := by
  have e1 : (List.range (k₁ + 1)).map g₁ ++ (List.range (k₂ + 1)).map g₂ ++ [b] =
      g₁ 0 :: ((List.range k₁).map (fun i ↦ g₁ (i + 1)) ++
        (g₂ 0 :: ((List.range k₂).map (fun i ↦ g₂ (i + 1)) ++ [b]))) := by
    rw [map_range_succ_twKConnected g₁ k₁, map_range_succ_twKConnected g₂ k₂]
    simp
  rw [e1, List.zipWith_cons_cons, zipWith_map_range_twKConnected, List.zipWith_cons_cons]
  have e2 := zipWith_map_range_twKConnected f g₂ k₂ [] [b]
  rw [List.append_nil] at e2
  rw [e2]
  simp

/-- A transposition does not depend on the order of its two points. -/
private theorem swap_eq_swap_twKConnected {x y x' y' : ℕ}
    (h : (x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) : Equiv.swap x y = Equiv.swap x' y' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Equiv.swap_comm _ _

/-- Equality of five-fold concatenations. -/
private theorem append_five_congr_twKConnected {α : Type*} {l₁ l₂ l₃ l₄ l₅ m₁ m₂ m₃ m₄ m₅ : List α}
    (h₁ : l₁ = m₁) (h₂ : l₂ = m₂) (h₃ : l₃ = m₃) (h₄ : l₄ = m₄) (h₅ : l₅ = m₅) :
    l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₅ = m₁ ++ m₂ ++ m₃ ++ m₄ ++ m₅ := by
  subst h₁ h₂ h₃ h₄ h₅
  rfl

/-- The chain for a negative twist is the path `0, M+n-1, …, M, M+n, …, M+2n-1, j₀`. -/
private theorem twChain_neg_path_twKConnected (M j₀ k : ℕ) :
    ([SBlock.band 0 (M + (k + 1) - 1)] ++
      (List.range (k + 1 - 1)).map
        (fun i ↦ SBlock.band (M + (k + 1) - 2 - i) (M + (k + 1) - 1 - i)) ++
      [SBlock.band M (M + (k + 1))] ++
      (List.range (k + 1 - 1)).map
        (fun i ↦ SBlock.band (M + (k + 1) + i) (M + (k + 1) + 1 + i)) ++
      [SBlock.band j₀ (M + 2 * (k + 1) - 1)]).map blockSwapTwKConnected =
    List.zipWith Equiv.swap
      (0 :: ((List.range (k + 1)).map (fun i ↦ M + k - i) ++
        (List.range (k + 1)).map (fun i ↦ M + k + 1 + i)))
      ((List.range (k + 1)).map (fun i ↦ M + k - i) ++
        (List.range (k + 1)).map (fun i ↦ M + k + 1 + i) ++ [j₀]) := by
  rw [zipWith_two_runs_twKConnected]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Nat.add_sub_cancel]
  refine append_five_congr_twKConnected ?_ ?_ ?_ ?_ ?_
  · exact congrArg (fun x ↦ [x]) (swap_eq_swap_twKConnected (by omega))
  · refine List.map_congr_left fun i hi ↦ swap_eq_swap_twKConnected ?_
    have := List.mem_range.1 hi
    omega
  · exact congrArg (fun x ↦ [x]) (swap_eq_swap_twKConnected (by omega))
  · refine List.map_congr_left fun i hi ↦ swap_eq_swap_twKConnected ?_
    have := List.mem_range.1 hi
    omega
  · exact congrArg (fun x ↦ [x]) (swap_eq_swap_twKConnected (by omega))

/-- The chain for a positive twist is the path `0, M+n+1, …, M+2n+3, M+n, …, M, j₀`. -/
private theorem twChain_pos_path_twKConnected (M j₀ n : ℕ) :
    ([SBlock.band 0 (M + n + 1)] ++
      (List.range (n + 2)).map (fun i ↦ SBlock.neg (M + n + 1 + i)) ++
      [SBlock.band (M + n) (M + 2 * n + 3)] ++
      (List.range n).map (fun i ↦ SBlock.neg (M + n - 1 - i)) ++
      [SBlock.band j₀ M]).map blockSwapTwKConnected =
    List.zipWith Equiv.swap
      (0 :: ((List.range (n + 2 + 1)).map (fun i ↦ M + n + 1 + i) ++
        (List.range (n + 1)).map (fun i ↦ M + n - i)))
      ((List.range (n + 2 + 1)).map (fun i ↦ M + n + 1 + i) ++
        (List.range (n + 1)).map (fun i ↦ M + n - i) ++ [j₀]) := by
  rw [zipWith_two_runs_twKConnected]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  refine append_five_congr_twKConnected ?_ ?_ ?_ ?_ ?_
  · exact congrArg (fun x ↦ [x]) (swap_eq_swap_twKConnected (by omega))
  · refine List.map_congr_left fun i hi ↦ swap_eq_swap_twKConnected ?_
    have := List.mem_range.1 hi
    omega
  · exact congrArg (fun x ↦ [x]) (swap_eq_swap_twKConnected (by omega))
  · refine List.map_congr_left fun i hi ↦ swap_eq_swap_twKConnected ?_
    have := List.mem_range.1 hi
    omega
  · exact congrArg (fun x ↦ [x]) (swap_eq_swap_twKConnected (by omega))

/-- Two monotone runs on disjoint ranges of new levels. -/
private theorem two_runs_path_twKConnected (M e : ℕ) (g₁ g₂ : ℕ → ℕ) (k₁ k₂ : ℕ)
    (h₁ : ∀ i < k₁, ∀ j < k₁, g₁ i = g₁ j → i = j) (h₂ : ∀ i < k₂, ∀ j < k₂, g₂ i = g₂ j → i = j)
    (h₁₂ : ∀ i < k₁, ∀ j < k₂, g₁ i ≠ g₂ j) (hM₁ : ∀ i < k₁, M ≤ g₁ i)
    (hM₂ : ∀ i < k₂, M ≤ g₂ i)
    (hcov : ∀ x, M ≤ x → x < M + e → (∃ i < k₁, g₁ i = x) ∨ ∃ i < k₂, g₂ i = x) :
    ((List.range k₁).map g₁ ++ (List.range k₂).map g₂).Nodup ∧
      (∀ p ∈ (List.range k₁).map g₁ ++ (List.range k₂).map g₂, M ≤ p) ∧
      ∀ x, M ≤ x → x < M + e → x ∈ (List.range k₁).map g₁ ++ (List.range k₂).map g₂ := by
  simp only [List.nodup_append, List.mem_append, List.mem_map, List.mem_range]
  refine ⟨⟨List.nodup_range.map_on fun x hx y hy ↦ h₁ x (List.mem_range.1 hx) y
    (List.mem_range.1 hy), List.nodup_range.map_on fun x hx y hy ↦ h₂ x (List.mem_range.1 hx) y
    (List.mem_range.1 hy), ?_⟩, ?_, hcov⟩
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact h₁₂ i hi j hj
  · rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact hM₁ i hi
    · exact hM₂ i hi

/-- The chain is a path from `0` to `j₀` through all the new levels. -/
private theorem twChain_path_twKConnected (M j₀ : ℕ) (ℓ : ℤ) :
    ∃ path : List ℕ, path.Nodup ∧ (∀ p ∈ path, M ≤ p) ∧
      (∀ x, M ≤ x → x < M + twExtra ℓ → x ∈ path) ∧
      (twChain M j₀ ℓ).map blockSwapTwKConnected =
        List.zipWith Equiv.swap (0 :: path) (path ++ [j₀]) := by
  rcases lt_trichotomy ℓ 0 with hl | rfl | hl
  · have hn : 1 ≤ ℓ.natAbs := Int.natAbs_pos.2 hl.ne
    rw [twChain, ite_eq_right hl.ne, ite_eq_left hl, twExtra, ite_eq_left hl.le]
    generalize ℓ.natAbs = n at hn ⊢
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨h1, h2, h3⟩ := two_runs_path_twKConnected M (2 * (k + 1)) (fun i ↦ M + k - i)
      (fun i ↦ M + k + 1 + i) (k + 1) (k + 1) (fun i hi j hj h ↦ by omega)
      (fun i hi j hj h ↦ by omega) (fun i hi j hj ↦ by omega)
      (fun i hi ↦ by omega) (fun i hi ↦ by omega)
      (fun x hx hx' ↦ by
        by_cases hxk : x ≤ M + k
        · exact Or.inl ⟨M + k - x, by omega, by omega⟩
        · exact Or.inr ⟨x - (M + k + 1), by omega, by omega⟩)
    exact ⟨_, h1, h2, h3, twChain_neg_path_twKConnected M j₀ k⟩
  · exact ⟨[], List.nodup_nil, by simp, by simp [twExtra], by simp [twChain, blockSwapTwKConnected]⟩
  · rw [twChain, ite_eq_right hl.ne', ite_eq_right hl.not_gt, twExtra, ite_eq_right hl.not_ge]
    generalize ℓ.natAbs = n
    obtain ⟨h1, h2, h3⟩ := two_runs_path_twKConnected M (2 * n + 4) (fun i ↦ M + n + 1 + i)
      (fun i ↦ M + n - i) (n + 2 + 1) (n + 1) (fun i hi j hj h ↦ by omega)
      (fun i hi j hj h ↦ by omega) (fun i hi j hj ↦ by omega)
      (fun i hi ↦ by omega) (fun i hi ↦ by omega)
      (fun x hx hx' ↦ by
        by_cases hxk : x ≤ M + n
        · exact Or.inr ⟨M + n - x, by omega, by omega⟩
        · exact Or.inl ⟨x - (M + n + 1), by omega, by omega⟩)
    exact ⟨_, h1, h2, h3, twChain_pos_path_twKConnected M j₀ n⟩

/-- Every position is reached from `0` by the permutation of the blocks of the twisted word. -/
private theorem exists_pow_blocksPerm_twKConnected {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ)
    (σ : Bool) {x : ℕ} (hx : x < twStrands r s ℓ) :
    ∃ n : ℕ, (blocksPermTwKConnected (twBlocks r s ℓ σ) ^ n) 0 = x := by
  have hv := pairBlocks_valid h
  have hhead : (SBlock.band 0 (twHeadTop r s)).Valid (pairStrands r s) :=
    hv _ (by rw [pairBlocks_eq_head_cons h]; exact List.mem_cons_self)
  simp only [SBlock.Valid] at hhead
  have hvt : ∀ b ∈ (pairBlocks r s).tail, b.Valid (pairStrands r s) := fun b hb ↦
    hv b (List.mem_of_mem_tail hb)
  obtain ⟨path, hnd, hM, hcov, hchain⟩ :=
    twChain_path_twKConnected (pairStrands r s) (twHeadTop r s) ℓ
  set R := blocksPermTwKConnected (pairBlocks r s).tail with hRdef
  have hRfix : ∀ t, pairStrands r s ≤ t → R t = t := fun t ht ↦
    blocksPermTwKConnected_of_le _ hvt ht
  have hold : blocksPermTwKConnected (pairBlocks r s) = Equiv.swap 0 (twHeadTop r s) * R := by
    conv_lhs => rw [pairBlocks_eq_head_cons h]
    rfl
  have hnew : blocksPermTwKConnected (twBlocks r s ℓ σ) =
      (List.zipWith Equiv.swap (0 :: path) (path ++ [twHeadTop r s])).prod * R := by
    rw [twBlocks, blocksPermTwKConnected_append, blocksPermTwKConnected_map_clasp, ← hchain]
    rfl
  have hreach : ∀ y, y < pairStrands r s →
      ∃ n : ℕ, ((Equiv.swap 0 (twHeadTop r s) * R) ^ n) 0 = y := by
    intro y hy
    obtain ⟨n, hn⟩ := connected_pairWhiteheadWord h ⟨0, by omega⟩ ⟨y, hy⟩
    refine ⟨n, ?_⟩
    have := strandPerm_pow_val_twKConnected (pairBlocks r s) hv n ⟨0, by omega⟩
    rw [← hold, ← this]
    exact congrArg Fin.val hn
  obtain ⟨h1, h2⟩ := exists_pow_swap_path_pointwise_twKConnected 0 path R (twHeadTop r s) hnd
    (fun hmem ↦ by have := hM _ hmem; omega) (fun hmem ↦ by have := hM _ hmem; omega)
    (by omega) (fun p hp ↦ hRfix p (hM p hp))
  rw [hnew]
  by_cases hxM : x < pairStrands r s
  · exact h1 x (fun hmem ↦ by have := hM _ hmem; omega) (hreach x hxM)
  · refine h2 x (hcov x (by omega) hx) (hreach _ ?_)
    by_contra hge
    have := hRfix _ (not_lt.1 hge)
    rw [show R (R⁻¹ 0) = 0 from R.apply_symm_apply 0] at this
    omega

/-- The closure of `twWhiteheadWord r s ℓ σ` has one component. -/
theorem connected_twWhiteheadWord {r s : ℕ} (h : IsTorusPair r s) (ℓ : ℤ) (σ : Bool)
    (i j : Fin (twStrands r s ℓ)) :
    ∃ n : ℕ, (strandPerm (twStrands r s ℓ) (twWhiteheadWord r s ℓ σ) ^ n) i = j := by
  have hpos : 0 < twStrands r s ℓ := i.pos
  have key : ∀ x : Fin (twStrands r s ℓ),
      (strandPerm (twStrands r s ℓ) (twWhiteheadWord r s ℓ σ)).SameCycle ⟨0, hpos⟩ x := by
    intro x
    obtain ⟨n, hn⟩ := exists_pow_blocksPerm_twKConnected h ℓ σ x.isLt
    refine ⟨n, ?_⟩
    rw [zpow_natCast]
    exact Fin.ext ((strandPerm_pow_val_twKConnected _ (twBlocks_valid h ℓ σ) n ⟨0, hpos⟩).trans hn)
  exact ((key i).symm.trans (key j)).exists_nat_pow_eq

end AJConjecture
