import Mathlib
import AJHandoff.TorusKnot.PairKIsoWords

/-!
# The torus braid read backwards

`(σ_{r-2} ⋯ σ₀)^s = Δ' (σ₀ ⋯ σ_{r-2})^s Δ'⁻¹` in the braid group, where `Δ'` is the Garside
braid of `σ₁, …, σ_{r-2}` (it fixes the strand `0`): from `Δ = Δ' δ` and `δ̄ Δ = Δ δ`
(`δ = σ₀ ⋯ σ_{r-2}`, `δ̄ = σ_{r-2} ⋯ σ₀`, `Δ` the Garside braid),
`δ̄^s Δ' = δ̄^s Δ δ⁻¹ = Δ δ^{s-1} = Δ' δ^s`. As a Morse reachability on `r` strands: `r2`, `r3` and far commutations (exchanges),
by induction on `r` and `s`.
-/

namespace AJConjecture

/-- The torus braid word read backwards, `(σ_{r-2} ⋯ σ₀)^s`. -/
def pairRevTorusWord (r s : ℕ) : BraidWord :=
  (List.replicate s ((List.range (r - 1)).reverse.map fun i ↦ (i, true))).flatten

/-- The Garside braid of `σ₁, …, σ_{r-2}`: `(σ_{r-2} ⋯ σ₁)(σ_{r-2} ⋯ σ₂) ⋯ (σ_{r-2})`. -/
def pairGarsideTail (r : ℕ) : BraidWord :=
  (List.range (r - 2)).flatMap fun a ↦
    ((List.range (r - 2 - a)).reverse.map fun i ↦ (i + 1 + a, true))

/-- The inverse of a braid word. -/
def isoBraidInv (w : BraidWord) : BraidWord := w.reverse.map fun g ↦ (g.1, !g.2)

/-- A braid word on `n` strands fits on `n` strands as a Morse word. -/
private theorem morseFits_braid_cb {n : ℕ} {w : BraidWord} (hw : IsOnStrands n w) :
    morseFits n (morseOfBraid w) = true := by
  refine morseFits_of_cross n _ (fun b hb ↦ ?_) fun b hb ↦ ?_
  · obtain ⟨g, -, rfl⟩ := List.mem_map.mp hb
    exact ⟨_, rfl⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    have := hw g hg
    dsimp only
    omega

/-- A braid word keeps the number of strands. -/
private theorem morseOut_braid_cb (n : ℕ) (w : BraidWord) : morseOut n (morseOfBraid w) = n := by
  refine morseOut_of_cross n _ fun b hb ↦ ?_
  obtain ⟨g, -, rfl⟩ := List.mem_map.mp hb
  exact ⟨_, rfl⟩

/-- Reachability between braid words holds in every braid context. -/
private theorem morseReach_braid_ctx {n : ℕ} (u v w w' : BraidWord)
    (hw : IsOnStrands n w) (h : MorseReach n (morseOfBraid w) (morseOfBraid w')) :
    MorseReach n (morseOfBraid (u ++ w ++ v)) (morseOfBraid (u ++ w' ++ v)) := by
  have h0 : ∀ x : MorseWord, morseShiftWord 0 x = x := fun x ↦ by
    unfold morseShiftWord
    induction x with
    | nil => rfl
    | cons a x ih => rw [List.map_cons, ih]; rfl
  have := morseReach_frame n n 0 0 (morseOfBraid u) (morseOfBraid v) _ _ h
    (morseFits_braid_cb hw) (by rw [morseOut_braid_cb]; omega)
  rw [h0, h0] at this
  simpa only [morseOfBraid, List.map_append] using this

/-- A braid word followed by its inverse cancels by `r2` moves. -/
private theorem morseReach_braid_cancel {n : ℕ} (w : BraidWord) (hw : IsOnStrands n w) :
    MorseReach n (morseOfBraid (w ++ isoBraidInv w)) [] := by
  induction w with
  | nil => exact morseReach_refl n _
  | cons g w ih =>
    have hw' : IsOnStrands n w := fun x hx ↦ hw x (List.mem_cons_of_mem _ hx)
    have hg := hw g List.mem_cons_self
    have h1 := morseReach_braid_ctx [g] [(g.1, !g.2)] (w ++ isoBraidInv w) [] (by
        intro x hx
        simp only [isoBraidInv, List.mem_append, List.mem_map, List.mem_reverse] at hx
        rcases hx with hx | ⟨y, hy, rfl⟩
        · exact hw' x hx
        · exact hw' y hy) (by simpa [morseOfBraid] using ih hw')
    have h2 := morseReach_isoRule n [] [] (.r2 g.1 g.2) rfl
      (morseFits_braid_cb (w := [g, (g.1, !g.2)]) (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> exact hg)) rfl
    refine morseReach_trans ?_ (morseReach_trans h1 ?_)
    · simp only [isoBraidInv, morseOfBraid, List.cons_append, List.reverse_cons, List.map_cons,
        List.map_append, List.append_assoc, List.nil_append, List.map_nil]
      exact morseReach_refl _ _
    · simpa [morseOfBraid, morseRuleLhs, morseRuleRhs] using h2

/-- The descending run `σ_m ⋯ σ_{j+1}` (empty for `j ≥ m`). -/
private def garsideRun (m j : ℕ) : BraidWord :=
  (List.range (m - j)).reverse.map fun i ↦ (i + 1 + j, true)

/-- The letters of a descending run lie on `m + 2` strands. -/
private theorem garsideRun_on {n m j : ℕ} (h : m + 2 ≤ n) : IsOnStrands n (garsideRun m j) := by
  intro g hg
  simp only [garsideRun, List.mem_map, List.mem_reverse, List.mem_range] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  dsimp only
  omega

/-- Peeling the bottom letter of a reversed range. -/
private theorem range_succ_reverse_map_cb {α : Type*} (f : ℕ → α) (t : ℕ) :
    (List.range (t + 1)).reverse.map f =
      (List.range t).reverse.map (fun i ↦ f (i + 1)) ++ [f 0] := by
  simp [List.range_succ_eq_map, Function.comp_def]

/-- A braid word as a Morse word distributes over concatenation. -/
private theorem morseOfBraid_append_cb (u v : BraidWord) :
    morseOfBraid (u ++ v) = morseOfBraid u ++ morseOfBraid v :=
  List.map_append

/-- A descending run ends one letter lower than the next run. -/
private theorem garsideRun_succ {m j : ℕ} (hj : j < m) :
    garsideRun m (j + 1) ++ [(j + 1, true)] = garsideRun m j := by
  obtain ⟨t, ht⟩ : ∃ t, m - j = t + 1 := ⟨m - j - 1, by omega⟩
  have ht' : m - (j + 1) = t := by omega
  rw [garsideRun, garsideRun, ht, ht', range_succ_reverse_map_cb]
  congr 1
  · exact List.map_congr_left fun i _ ↦ by simp only [Prod.mk.injEq, and_true]; omega
  · simp only [List.cons.injEq, Prod.mk.injEq, and_true]
    omega

/-- The runs ending in their last letters are `δ̄` followed by the runs. -/
private theorem flatMap_garsideRun_letter (m : ℕ) :
    ∀ k ≤ m, (List.range (k + 1)).flatMap (fun j ↦ garsideRun m j ++ [(j, true)]) =
      (List.range (m + 1)).reverse.map (fun i ↦ (i, true)) ++
        (List.range k).flatMap (garsideRun m)
  | 0, _ => by
    simp only [zero_add, List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.range_zero, range_succ_reverse_map_cb, garsideRun, Nat.sub_zero, add_zero]
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, flatMap_garsideRun_letter m k (by omega),
      List.range_succ (n := k), List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
      garsideRun_succ (show k < m by omega)]

/-- The run letters move to the end past the later runs by far commutations. -/
private theorem morseReach_garsideRun_commute {n m : ℕ} (hm : m + 2 ≤ n) :
    ∀ k ≤ m + 1, MorseReach n
      (morseOfBraid ((List.range k).flatMap (fun j ↦ garsideRun m j ++ [(j, true)])))
      (morseOfBraid ((List.range k).flatMap (garsideRun m) ++
        (List.range k).map (fun i ↦ (i, true))))
  | 0, _ => morseReach_refl n _
  | k + 1, hk => by
    have hA : IsOnStrands n ((List.range k).map (fun i ↦ (i, true))) := by
      intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
      rw [List.mem_range] at hi
      dsimp only
      omega
    have hG : IsOnStrands n ((List.range k).flatMap (fun j ↦ garsideRun m j ++ [(j, true)])) := by
      intro g hg
      obtain ⟨j, hj, hg⟩ := List.mem_flatMap.mp hg
      rw [List.mem_range] at hj
      rcases List.mem_append.mp hg with hg | hg
      · exact garsideRun_on hm g hg
      · rw [List.mem_singleton] at hg
        subst hg
        dsimp only
        omega
    have h1 := morseReach_braid_ctx [] (garsideRun m k ++ [(k, true)]) _ _ hG
      (morseReach_garsideRun_commute hm k (by omega))
    have h2 := morseReach_comm n (morseOfBraid ((List.range k).flatMap (garsideRun m)))
      (morseOfBraid ((List.range k).map (fun i ↦ (i, true)))) (morseOfBraid (garsideRun m k))
      (morseOfBraid [(k, true)]) (fun b hb ↦ by
        obtain ⟨g, -, rfl⟩ := List.mem_map.mp hb
        exact ⟨_, rfl⟩) (fun b hb a ha ↦ by
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp ha
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
        simp only [garsideRun, List.mem_map, List.mem_reverse, List.mem_range] at hg'
        obtain ⟨i', hi', rfl⟩ := hg'
        rw [List.mem_range] at hi
        dsimp only
        omega) (by
        rw [morseOut_braid_cb, ← morseOfBraid_append_cb]
        exact morseFits_braid_cb fun g hg ↦ by
          rcases List.mem_append.mp hg with hg | hg
          · exact garsideRun_on hm g hg
          · exact hA g hg)
    refine morseReach_trans ?_ (morseReach_trans (morseReach_symm h2) ?_)
    · simpa only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.nil_append, morseOfBraid, List.map_append, List.append_assoc]
        using h1
    · simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.map_append, morseOfBraid, List.append_assoc, List.map_cons,
        List.map_nil]
      exact morseReach_refl n _

/-- `δ̄ Δ' = Δ' δ` by far commutations. -/
private theorem morseReach_garside_conj {n m : ℕ} (hm : m + 2 ≤ n) :
    MorseReach n (morseOfBraid ((List.range (m + 1)).reverse.map (fun i ↦ (i, true)) ++
        (List.range m).flatMap (garsideRun m)))
      (morseOfBraid ((List.range m).flatMap (garsideRun m) ++
        (List.range (m + 1)).map (fun i ↦ (i, true)))) := by
  have h := morseReach_garsideRun_commute hm (m + 1) le_rfl
  have hG : (List.range (m + 1)).flatMap (garsideRun m) =
      (List.range m).flatMap (garsideRun m) := by
    rw [List.range_succ, List.flatMap_append]
    simp [garsideRun]
  rwa [flatMap_garsideRun_letter m m le_rfl, hG] at h

/-- A repeated word on `n` strands is on `n` strands. -/
private theorem isOnStrands_flatten_replicate_cb {n s : ℕ} {x : BraidWord} (hx : IsOnStrands n x) :
    IsOnStrands n (List.replicate s x).flatten := by
  intro g hg
  obtain ⟨l, hl, hg⟩ := List.mem_flatten.mp hg
  rw [(List.mem_replicate.mp hl).2] at hg
  exact hx g hg

/-- A word followed by its inverse is on the strands of the word. -/
private theorem isOnStrands_append_inv_cb {n : ℕ} {x : BraidWord} (hx : IsOnStrands n x) :
    IsOnStrands n (x ++ isoBraidInv x) := by
  intro g hg
  simp only [isoBraidInv, List.mem_append, List.mem_map, List.mem_reverse] at hg
  rcases hg with hg | ⟨y, hy, rfl⟩
  · exact hx g hg
  · exact hx y hy

/-- `δ̄^s Δ' = Δ' δ^s` by far commutations. -/
private theorem morseReach_garside_pow {n m : ℕ} (hm : m + 2 ≤ n) :
    ∀ s, MorseReach n
      (morseOfBraid
        ((List.replicate s ((List.range (m + 1)).reverse.map (fun i ↦ (i, true)))).flatten ++
          (List.range m).flatMap (garsideRun m)))
      (morseOfBraid ((List.range m).flatMap (garsideRun m) ++
        (List.replicate s ((List.range (m + 1)).map (fun i ↦ (i, true)))).flatten))
  | 0 => by simpa using morseReach_refl n _
  | s + 1 => by
    have hR : IsOnStrands n
        (List.replicate s ((List.range (m + 1)).reverse.map (fun i ↦ (i, true)))).flatten := by
      refine isOnStrands_flatten_replicate_cb fun g hg ↦ ?_
      simp only [List.mem_map, List.mem_reverse, List.mem_range] at hg
      obtain ⟨i, hi, rfl⟩ := hg
      dsimp only
      omega
    have hRG : IsOnStrands n
        ((List.replicate s ((List.range (m + 1)).reverse.map (fun i ↦ (i, true)))).flatten ++
          (List.range m).flatMap (garsideRun m)) := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hR g hg
      · obtain ⟨j, -, hg⟩ := List.mem_flatMap.mp hg
        exact garsideRun_on hm g hg
    have hD : IsOnStrands n ((List.range (m + 1)).reverse.map (fun i ↦ (i, true)) ++
        (List.range m).flatMap (garsideRun m)) := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · simp only [List.mem_map, List.mem_reverse, List.mem_range] at hg
        obtain ⟨i, hi, rfl⟩ := hg
        dsimp only
        omega
      · obtain ⟨j, -, hg⟩ := List.mem_flatMap.mp hg
        exact garsideRun_on hm g hg
    have h1 := morseReach_braid_ctx
      (List.replicate s ((List.range (m + 1)).reverse.map (fun i ↦ (i, true)))).flatten [] _ _ hD
      (morseReach_garside_conj hm)
    have h2 := morseReach_braid_ctx [] ((List.range (m + 1)).map (fun i ↦ (i, true))) _ _ hRG
      (morseReach_garside_pow hm s)
    simp only [List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.append_assoc, List.nil_append] at h1 h2 ⊢
    exact morseReach_trans h1 h2

/-- `(σ_{r-2} ⋯ σ₀)^s` and `Δ' (σ₀ ⋯ σ_{r-2})^s Δ'⁻¹` are related by braid moves. -/
theorem morseReach_pairRevTorusWord (r s : ℕ) (hr : 2 ≤ r) :
    MorseReach r (morseOfBraid (pairRevTorusWord r s))
      (morseOfBraid (pairGarsideTail r ++ torusPairWord r s ++
        isoBraidInv (pairGarsideTail r))) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have hG : pairGarsideTail (m + 2) = (List.range m).flatMap (garsideRun m) := rfl
  have hm1 : m + 2 - 1 = m + 1 := rfl
  have hGo : IsOnStrands (m + 2) ((List.range m).flatMap (garsideRun m)) := fun g hg ↦ by
    obtain ⟨j, -, hg⟩ := List.mem_flatMap.mp hg
    exact garsideRun_on le_rfl g hg
  have hR : IsOnStrands (m + 2) (pairRevTorusWord (m + 2) s) := by
    refine isOnStrands_flatten_replicate_cb fun g hg ↦ ?_
    simp only [hm1, List.mem_map, List.mem_reverse, List.mem_range] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    dsimp only
    omega
  have h1 := morseReach_braid_ctx (pairRevTorusWord (m + 2) s) []
    ((List.range m).flatMap (garsideRun m) ++ isoBraidInv ((List.range m).flatMap (garsideRun m)))
    [] (isOnStrands_append_inv_cb hGo) (morseReach_braid_cancel _ hGo)
  have h2 := morseReach_braid_ctx [] (isoBraidInv ((List.range m).flatMap (garsideRun m))) _ _
    (fun g hg ↦ by
      rcases List.mem_append.mp hg with hg | hg
      · exact hR g hg
      · exact hGo g hg) (morseReach_garside_pow le_rfl s)
  rw [hG]
  simp only [List.append_nil, List.nil_append, List.append_assoc] at h1 h2
  refine morseReach_trans (morseReach_symm h1) ?_
  simpa only [pairRevTorusWord, torusPairWord, hm1, List.append_assoc] using h2

end AJConjecture
