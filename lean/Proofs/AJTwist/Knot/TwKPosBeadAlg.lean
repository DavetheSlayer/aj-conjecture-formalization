import Mathlib
import AJTwist.Knot.TwKPosWrap
import AJTwist.Knot.TwKTargetOp
import AJHandoff.TorusKnot.PairKIsoCompanion

/-!
# The operator of an evacuated word

After the evacuation the word is `u1 · twists · morseDouble G · L.flatten · n1`, where `L` lists
`N` blocks `A1`, `N` positive curls and the clasp of sign `σ` in an unknown order, each bead as it
is or rotated. `morseOp_twkEvacuated`: its thick operator is that of the band-and-clasp word over
`G` with `2N` more negative half twists, whatever the order.

Proof (operators on the band, notation of `TwKPosBeadOps`). By `morseOp_twkBracket` both sides
are partial traces. Every bead other than the clasp is a monomial in `D, P₀, P₁, Q₀, Q₁`
(`A1 = D Q₁`, rotated `Q₀ D`; the curl `P₁`, rotated `P₀`), and these commute; the clasp is
invariant under the rotation. So `twkOp c L.flatten = D^a m K D^b m'` with `a + b = N` and
monomials `m, m'` in the curls whose total exponent is `N - N = 0` (induction over the list
`L`: `twkOp_append`). Then
1. `K D^b = D^b (Q₀ Q₁)^b K (P₁ P₀)^b` (`twkOp_clasp_twist`);
2. above the clasp the curls go to the second strand (`twkOp_clasp_curl`), pass to the bottom
   end under the partial trace (`ptrTail_twkOp_curl_comm`), commute with the doubled core and
   with the twists (`twkOp_morseDouble_commute`) and reach the clasp from below;
3. below the clasp the curls go to one strand (`twkOp_curl_clasp`) and cancel
   (`twkOp_curl_inv`): the total exponent is zero;
4. `twists · D^N = twTwistWord (k - 2N)` and the doubled core commutes with the twists.

`morseOp_twkCoreTarget`: for the torus core the band-and-clasp word over `pairCore r s` has the
operator of `twTargetWord r s k σ` (`morseReach_pairCore_torus`, doubled by
`morseReach_morseDouble` and framed, as `morseReach_pairWE_target`).

Checked outside Lean (`SCR/KP/tools/alg_test.py`): 152 random orders and rotations, `N ≤ 3`,
both clasp signs, even and odd numbers of half twists, four cores, thickness one and two.
-/

noncomputable section

namespace AJConjecture

/-- A one-parameter family that fixes `K` on the left at `±1` fixes it everywhere. -/
private theorem zhom_fix_left_beadAlg {R : Type*} [Monoid R] (f : ℤ → R) (K : R)
    (hf : ∀ m m', f (m + m') = f m * f m') (h1 : f 1 * K = K) (h1' : f (-1) * K = K) :
    ∀ m : ℤ, f m * K = K := by
  have h0 : f 0 * K = K := by
    have h := hf 1 (-1)
    rw [show (1 : ℤ) + -1 = 0 by norm_num] at h
    rw [h, mul_assoc, h1', h1]
  intro m
  induction m using Int.induction_on with
  | zero => exact h0
  | succ n ih => rw [hf, mul_assoc, h1, ih]
  | pred n ih => rw [sub_eq_add_neg, hf, mul_assoc, h1', ih]

/-- A one-parameter family that fixes `K` on the right at `±1` fixes it everywhere. -/
private theorem zhom_fix_right_beadAlg {R : Type*} [Monoid R] (f : ℤ → R) (K : R)
    (hf : ∀ m m', f (m + m') = f m * f m') (h1 : K * f 1 = K) (h1' : K * f (-1) = K) :
    ∀ m : ℤ, K * f m = K := by
  have h0 : K * f 0 = K := by
    have h := hf 1 (-1)
    rw [show (1 : ℤ) + -1 = 0 by norm_num] at h
    rw [h, ← mul_assoc, h1, h1']
  intro m
  induction m using Int.induction_on with
  | zero => exact h0
  | succ n ih => rw [hf, ← mul_assoc, ih, h1]
  | pred n ih => rw [sub_eq_add_neg, hf, ← mul_assoc, ih, h1']

/-- Two one-parameter families intertwined by `T` at `1` are intertwined everywhere. -/
private theorem zhom_semiconj_beadAlg {R : Type*} [Monoid R] (f g : ℤ → R) (T : R)
    (hf : ∀ m m', f (m + m') = f m * f m') (hg : ∀ m m', g (m + m') = g m * g m')
    (hf0 : f 0 = 1) (hg0 : g 0 = 1) (h1 : f 1 * T = T * g 1) : ∀ m : ℤ, f m * T = T * g m := by
  have hf1 : f (-1) * f 1 = 1 := by rw [← hf, ← hf0]; norm_num
  have hg1 : g 1 * g (-1) = 1 := by rw [← hg, ← hg0]; norm_num
  have h1' : f (-1) * T = T * g (-1) := by
    calc f (-1) * T = f (-1) * (T * g 1) * g (-1) := by
          rw [mul_assoc, mul_assoc, hg1, mul_one]
      _ = T * g (-1) := by rw [← h1, ← mul_assoc, hf1, one_mul]
  intro m
  induction m using Int.induction_on with
  | zero => rw [hf0, hg0, one_mul, mul_one]
  | succ n ih => rw [hf, hg, mul_assoc, h1, ← mul_assoc, ih, mul_assoc]
  | pred n ih => rw [sub_eq_add_neg, hf, hg, mul_assoc, h1', ← mul_assoc, ih, mul_assoc]

/-- A trace-like function that is cyclic for a one-parameter family at `±1` is cyclic for the
whole family. -/
private theorem zhom_trace_beadAlg {R S : Type*} [Monoid R] (τ : R → S) (f : ℤ → R)
    (hf : ∀ m m', f (m + m') = f m * f m') (hf0 : f 0 = 1)
    (h1 : ∀ M, τ (M * f 1) = τ (f 1 * M)) (h1' : ∀ M, τ (M * f (-1)) = τ (f (-1) * M)) :
    ∀ (m : ℤ) (M : R), τ (M * f m) = τ (f m * M) := by
  intro m
  induction m using Int.induction_on with
  | zero => intro M; rw [hf0, one_mul, mul_one]
  | succ n ih =>
    intro M
    rw [hf, ← mul_assoc, h1, ← mul_assoc, ih, mul_assoc]
  | pred n ih =>
    intro M
    rw [sub_eq_add_neg, hf, ← mul_assoc, h1', ← mul_assoc, ih, mul_assoc]

/-- The algebra of an evacuated word: twists and curls around a clasp under a partial trace. -/
private theorem evac_alg_beadAlg {R S : Type*} [Monoid R] (τ : R → S) (E : ℤ → ℤ → ℤ → R)
    (K B T : R) (hE0 : E 0 0 0 = 1)
    (hE : ∀ a i j a' i' j', E a i j * E a' i' j' = E (a + a') (i + i') (j + j'))
    (hK0 : E 0 1 0 * K = E 0 0 1 * K) (hK1 : K * E 0 1 0 = K * E 0 0 1)
    (hKd : K * E 1 0 0 = E 1 (-1) (-1) * K * E 0 1 1)
    (hτ : ∀ M, τ (M * E 0 0 1) = τ (E 0 0 1 * M))
    (hτ' : ∀ M, τ (M * E 0 0 (-1)) = τ (E 0 0 (-1) * M))
    (hT : E 0 0 1 * T = T * E 0 0 1 ∨ E 0 0 1 * T = T * E 0 1 0)
    (hB0 : E 0 1 0 * B = B * E 0 1 0) (hB1 : E 0 0 1 * B = B * E 0 0 1) (hBT : T * B = B * T)
    (a : ℤ) (b : ℕ) (i j i' j' : ℤ) (h0 : i + j + i' + j' = 0) :
    τ (T * B * E a i j * K * E b i' j') = τ (B * T * E (a + b) 0 0 * K) := by
  have mulE : ∀ a i j a' i' j' a'' i'' j'' : ℤ, a + a' = a'' → i + i' = i'' → j + j' = j'' →
      E a i j * E a' i' j' = E a'' i'' j'' := by
    intro a i j a' i' j' a'' i'' j'' h1 h2 h3
    rw [hE, h1, h2, h3]
  -- a curl changes the edge at the clasp, below and above
  have s1 : ∀ m : ℤ, E 0 m (-m) * K = K := by
    have e1 : E 0 0 (-1) * E 0 1 0 = E 0 1 (-1) :=
      mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
    have e2 : E 0 0 (-1) * E 0 0 1 = E 0 0 0 :=
      mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
    have e3 : E 0 (-1) 1 * E 0 1 (-1) = E 0 0 0 :=
      mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
    have h1 : E 0 1 (-1) * K = K := by
      rw [← e1, mul_assoc, hK0, ← mul_assoc, e2, hE0, one_mul]
    have h1' : E 0 (-1) (-(-1)) * K = K := by
      rw [neg_neg]
      calc E 0 (-1) 1 * K = E 0 (-1) 1 * (E 0 1 (-1) * K) := by rw [h1]
        _ = K := by rw [← mul_assoc, e3, hE0, one_mul]
    exact zhom_fix_left_beadAlg (fun m ↦ E 0 m (-m)) K
      (fun m m' ↦ (mulE 0 m (-m) 0 m' (-m') 0 (m + m') (-(m + m')) (by omega) rfl
        (by omega)).symm) h1 h1'
  have s2 : ∀ m : ℤ, K * E 0 m (-m) = K := by
    have e1 : E 0 1 0 * E 0 0 (-1) = E 0 1 (-1) :=
      mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
    have e2 : E 0 0 1 * E 0 0 (-1) = E 0 0 0 :=
      mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
    have e3 : E 0 1 (-1) * E 0 (-1) 1 = E 0 0 0 :=
      mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
    have h1 : K * E 0 1 (-1) = K := by
      rw [← e1, ← mul_assoc, hK1, mul_assoc, e2, hE0, mul_one]
    have h1' : K * E 0 (-1) (-(-1)) = K := by
      rw [neg_neg]
      calc K * E 0 (-1) 1 = K * E 0 1 (-1) * E 0 (-1) 1 := by rw [h1]
        _ = K := by rw [mul_assoc, e3, hE0, mul_one]
    exact zhom_fix_right_beadAlg (fun m ↦ E 0 m (-m)) K
      (fun m m' ↦ (mulE 0 m (-m) 0 m' (-m') 0 (m + m') (-(m + m')) (by omega) rfl
        (by omega)).symm) h1 h1'
  have s1L : ∀ a i j : ℤ, E a i j * K = E a 0 (i + j) * K := fun a i j ↦ by
    have e : E a 0 (i + j) * E 0 i (-i) = E a i j :=
      mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
    rw [← e, mul_assoc, s1]
  have s2R : ∀ i j : ℤ, K * E 0 i j = K * E 0 0 (i + j) := fun i j ↦ by
    have e : E 0 i (-i) * E 0 0 (i + j) = E 0 i j :=
      mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
    rw [← e, ← mul_assoc, s2]
  -- a twist passes the clasp
  have hKd' : K * E 1 0 0 = E 1 0 (-2) * K * E 0 0 2 := by
    rw [hKd, s1L 1 (-1) (-1), mul_assoc, s2R 1 1, ← mul_assoc]
    norm_num
  have s3 : ∀ n : ℕ, K * E n 0 0 = E n 0 (-2 * n) * K * E 0 0 (2 * n) := by
    intro n
    induction n with
    | zero => simp [hE0]
    | succ n ih =>
      have e1 : E n 0 0 * E 1 0 0 = E (n + 1 : ℕ) 0 0 :=
        mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
      have e2 : E 0 0 (2 * n) * E 1 0 0 = E 1 0 0 * E 0 0 (2 * n) :=
        (mulE _ _ _ _ _ _ 1 0 (2 * n) (by omega) (by omega) (by omega)).trans
          (mulE _ _ _ _ _ _ 1 0 (2 * n) (by omega) (by omega) (by omega)).symm
      have e3 : E n 0 (-2 * n) * E 1 0 (-2) = E (n + 1 : ℕ) 0 (-2 * (n + 1 : ℕ)) :=
        mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
      have e4 : E 0 0 2 * E 0 0 (2 * n) = E 0 0 (2 * (n + 1 : ℕ)) :=
        mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
      calc K * E (n + 1 : ℕ) 0 0 = K * E n 0 0 * E 1 0 0 := by rw [← e1, mul_assoc]
        _ = E n 0 (-2 * n) * K * (E 0 0 (2 * n) * E 1 0 0) := by rw [ih, mul_assoc]
        _ = E n 0 (-2 * n) * (K * E 1 0 0) * E 0 0 (2 * n) := by
          rw [e2]
          simp only [mul_assoc]
        _ = E n 0 (-2 * n) * E 1 0 (-2) * K * (E 0 0 2 * E 0 0 (2 * n)) := by
          rw [hKd']
          simp only [mul_assoc]
        _ = E (n + 1 : ℕ) 0 (-2 * (n + 1 : ℕ)) * K * E 0 0 (2 * (n + 1 : ℕ)) := by rw [e3, e4]
  -- curls pass around the trace, through the twists and through the core
  have s4 : ∀ (m : ℤ) (M : R), τ (M * E 0 0 m) = τ (E 0 0 m * M) :=
    zhom_trace_beadAlg τ (fun m ↦ E 0 0 m)
      (fun m m' ↦ (mulE 0 0 m 0 0 m' 0 0 (m + m') rfl rfl rfl).symm) hE0 hτ hτ'
  have s5 : ∀ m : ℤ, ∃ e₀ e₁ : ℤ, e₀ + e₁ = m ∧ E 0 0 m * T = T * E 0 e₀ e₁ := by
    intro m
    rcases hT with hT | hT
    · exact ⟨0, m, zero_add m, zhom_semiconj_beadAlg (fun m ↦ E 0 0 m) (fun m ↦ E 0 0 m) T
        (fun m m' ↦ (mulE 0 0 m 0 0 m' 0 0 (m + m') rfl rfl rfl).symm)
        (fun m m' ↦ (mulE 0 0 m 0 0 m' 0 0 (m + m') rfl rfl rfl).symm) hE0 hE0 hT m⟩
    · exact ⟨m, 0, add_zero m, zhom_semiconj_beadAlg (fun m ↦ E 0 0 m) (fun m ↦ E 0 m 0) T
        (fun m m' ↦ (mulE 0 0 m 0 0 m' 0 0 (m + m') rfl rfl rfl).symm)
        (fun m m' ↦ (mulE 0 m 0 0 m' 0 0 (m + m') 0 rfl rfl rfl).symm) hE0 hE0 hT m⟩
  have s6 : ∀ e₀ e₁ : ℤ, E 0 e₀ e₁ * B = B * E 0 e₀ e₁ := by
    intro e₀ e₁
    have ha := zhom_semiconj_beadAlg (fun m ↦ E 0 m 0) (fun m ↦ E 0 m 0) B
      (fun m m' ↦ (mulE 0 m 0 0 m' 0 0 (m + m') 0 rfl rfl rfl).symm)
      (fun m m' ↦ (mulE 0 m 0 0 m' 0 0 (m + m') 0 rfl rfl rfl).symm) hE0 hE0 hB0 e₀
    have hb := zhom_semiconj_beadAlg (fun m ↦ E 0 0 m) (fun m ↦ E 0 0 m) B
      (fun m m' ↦ (mulE 0 0 m 0 0 m' 0 0 (m + m') rfl rfl rfl).symm)
      (fun m m' ↦ (mulE 0 0 m 0 0 m' 0 0 (m + m') rfl rfl rfl).symm) hE0 hE0 hB1 e₁
    have e : E 0 e₀ 0 * E 0 0 e₁ = E 0 e₀ e₁ :=
      mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
    rw [← e, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  -- the computation
  obtain ⟨e₀, e₁, he, hTm⟩ := s5 (2 * b + i' + j')
  have y1 : E b 0 0 * E 0 i' j' = E b i' j' :=
    mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have y2 : E 0 0 (2 * b) * E 0 i' j' = E 0 i' (2 * b + j') :=
    mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have hY : K * E b i' j' = E b 0 (-2 * b) * K * E 0 0 (2 * b + i' + j') := by
    calc K * E b i' j' = K * E b 0 0 * E 0 i' j' := by rw [← y1, mul_assoc]
      _ = E b 0 (-2 * b) * (K * (E 0 0 (2 * b) * E 0 i' j')) := by
        rw [s3]
        simp only [mul_assoc]
      _ = E b 0 (-2 * b) * K * E 0 0 (2 * b + i' + j') := by
        rw [y2, s2R, ← mul_assoc, show i' + (2 * (b : ℤ) + j') = 2 * b + i' + j' by ring]
  have x1 : E a i j * E b 0 (-2 * b) = E (a + b) i (j - 2 * b) :=
    mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
  have x2 : E 0 e₀ e₁ * E (a + b) i (j - 2 * b) = E (a + b) (e₀ + i) (e₁ + (j - 2 * b)) :=
    mulE _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
  calc τ (T * B * E a i j * K * E b i' j')
      = τ (T * B * E (a + b) i (j - 2 * b) * K * E 0 0 (2 * b + i' + j')) := by
        rw [mul_assoc (T * B * E a i j), hY, ← x1]
        simp only [mul_assoc]
    _ = τ (E 0 0 (2 * b + i' + j') * (T * B * E (a + b) i (j - 2 * b) * K)) := s4 _ _
    _ = τ (T * B * (E 0 e₀ e₁ * E (a + b) i (j - 2 * b)) * K) := by
        congr 1
        calc E 0 0 (2 * b + i' + j') * (T * B * E (a + b) i (j - 2 * b) * K)
            = E 0 0 (2 * b + i' + j') * T * B * E (a + b) i (j - 2 * b) * K := by
              simp only [mul_assoc]
          _ = T * (E 0 e₀ e₁ * B) * E (a + b) i (j - 2 * b) * K := by
              rw [hTm]
              simp only [mul_assoc]
          _ = T * B * (E 0 e₀ e₁ * E (a + b) i (j - 2 * b)) * K := by
              rw [s6]
              simp only [mul_assoc]
    _ = τ (T * B * E (a + b) 0 0 * K) := by
        rw [x2, mul_assoc, s1L, ← mul_assoc,
          show e₀ + i + (e₁ + (j - 2 * (b : ℤ))) = 0 by omega]
    _ = τ (B * T * E (a + b) 0 0 * K) := by rw [hBT]

/-- A positive right curl on the first strand passes a crossing to the second strand. -/
private theorem morseReach_curlX_beadAlg (s : Bool) :
    MorseReach 2 (isoCurlR true 0 ++ [isoX s 0]) ([isoX s 0] ++ isoCurlR true 1) := by
  cases s
  · exact
    ⟨[(2, .capSlide 1 false false, true), (4, .exch (.cross false, 0) (.cap, 2), true),
      (5, .r2 1 false, true), (3, .r3 0 false, true),
      (2, .exch (.cross false, 0) (.cross false, 2), true), (1, .r2 0 true, false),
      (0, .cupSlide 1 false false, false), (0, .exch (.cross false, 0) (.cup, 2), true)],
      by decide⟩
  · exact
    ⟨[(2, .capSlide 1 true false, true), (1, .exch (.cross true, 0) (.cross true, 2), false),
      (4, .exch (.cross true, 0) (.cap, 2), true), (2, .r3 0 true, false),
      (0, .cupSlide 1 true false, false), (0, .exch (.cross true, 0) (.cup, 2), true)],
      by decide⟩

/-- A positive right curl on the first strand above a crossing comes from the second strand. -/
private theorem morseReach_xCurl_beadAlg (s : Bool) :
    MorseReach 2 ([isoX s 0] ++ isoCurlR true 0) (isoCurlR true 1 ++ [isoX s 0]) := by
  cases s
  · exact
    ⟨[(4, .r2 0 true, true), (3, .capSlide 1 true false, true),
      (2, .exch (.cross true, 0) (.cross true, 2), false),
      (5, .exch (.cross true, 0) (.cap, 2), true), (3, .r3 0 true, false),
      (1, .cupSlide 1 true false, false), (1, .exch (.cross true, 0) (.cup, 2), true),
      (0, .r2 0 false, false)],
      by decide⟩
  · exact
    ⟨[(4, .r2 0 false, true), (3, .capSlide 1 false false, true),
      (5, .exch (.cross false, 0) (.cap, 2), true), (6, .r2 1 false, true), (4, .r3 0 false, true),
      (3, .exch (.cross false, 0) (.cross false, 2), true), (2, .r2 0 true, false),
      (1, .cupSlide 1 false false, false), (1, .exch (.cross false, 0) (.cup, 2), true),
      (0, .r2 0 true, false)],
      by decide⟩

/-! ### The commuting operators of the band -/

/-- The positive curl on the first strand, as a unit. -/
private def beadCurl0U (c : ℕ) : (SkMat (2 * c) (2 * c))ˣ :=
  ⟨twkOp c (isoCurlR true 0), twkOp c (isoCurlR false 0), (twkOp_curl_inv c).2.2.1,
    (twkOp_curl_inv c).2.2.2⟩

/-- The positive curl on the second strand, as a unit. -/
private def beadCurl1U (c : ℕ) : (SkMat (2 * c) (2 * c))ˣ :=
  ⟨twkOp c (isoCurlL true 1), twkOp c (isoCurlL false 1), (twkOp_curl_inv c).1,
    (twkOp_curl_inv c).2.1⟩

/-- The negative full twist of the band and its inverse. -/
private theorem twkOp_twist_inv_beadAlg (c : ℕ) :
    twkOp c (twkTw 1) * twkOp c [isoX true 0, isoX true 0] = 1 ∧
      twkOp c [isoX true 0, isoX true 0] * twkOp c (twkTw 1) = 1 := by
  have h : twkOp c (twkTw 1) * twkOp c [isoX true 0, isoX true 0] = 1 := by
    rw [← twkOp_append c _ _ (by decide) (by decide), ← twkOp_nil c]
    exact twkOp_eq_of_morseReach
      ⟨[(1, .r2 0 false, false), (0, .r2 0 false, false)], by decide⟩ c
  exact ⟨h, mul_eq_one_comm.1 h⟩

/-- The negative full twist of the band, as a unit. -/
private def beadTwistU (c : ℕ) : (SkMat (2 * c) (2 * c))ˣ :=
  ⟨twkOp c (twkTw 1), twkOp c [isoX true 0, isoX true 0], (twkOp_twist_inv_beadAlg c).1,
    (twkOp_twist_inv_beadAlg c).2⟩

/-- The monomial `D^a P₀^i P₁^j` in the full twist and the curls. -/
private def beadMono (c : ℕ) (a i j : ℤ) : SkMat (2 * c) (2 * c) :=
  ((beadTwistU c ^ a * beadCurl0U c ^ i * beadCurl1U c ^ j : (SkMat (2 * c) (2 * c))ˣ) :
    SkMat (2 * c) (2 * c))

/-- The trivial monomial. -/
private theorem beadMono_zero (c : ℕ) : beadMono c 0 0 0 = 1 := by simp [beadMono]

/-- The monomial of the negative full twist. -/
private theorem beadMono_twist (c : ℕ) : beadMono c 1 0 0 = twkOp c (twkTw 1) := by
  simp [beadMono, beadTwistU]

/-- The monomial of the positive curl on the first strand. -/
private theorem beadMono_curl0 (c : ℕ) : beadMono c 0 1 0 = twkOp c (isoCurlR true 0) := by
  simp [beadMono, beadCurl0U]

/-- The monomial of the positive curl on the second strand. -/
private theorem beadMono_curl1 (c : ℕ) : beadMono c 0 0 1 = twkOp c (isoCurlL true 1) := by
  simp [beadMono, beadCurl1U]

/-- The monomial of the negative curl on the first strand. -/
private theorem beadMono_curl0_inv (c : ℕ) : beadMono c 0 (-1) 0 = twkOp c (isoCurlR false 0) := by
  simp [beadMono, beadCurl0U]

/-- The monomial of the negative curl on the second strand. -/
private theorem beadMono_curl1_inv (c : ℕ) : beadMono c 0 0 (-1) = twkOp c (isoCurlL false 1) := by
  simp [beadMono, beadCurl1U]

/-- A product of six elements that commute pairwise as needed, sorted. -/
private theorem mul_six_comm_beadAlg {U : Type*} [Monoid U] (x y z x' y' z' : U)
    (hzx : z * x' = x' * z) (hyx : y * x' = x' * y) (hzy : z * y' = y' * z) :
    x * y * z * (x' * y' * z') = x * x' * (y * y') * (z * z') := by
  calc x * y * z * (x' * y' * z') = x * y * (z * x') * y' * z' := by simp only [mul_assoc]
    _ = x * (y * x') * (z * y') * z' := by
      rw [hzx]
      simp only [mul_assoc]
    _ = x * x' * (y * y') * (z * z') := by
      rw [hyx, hzy]
      simp only [mul_assoc]

/-- The monomials multiply by adding the exponents. -/
private theorem beadMono_mul (c : ℕ) (a i j a' i' j' : ℤ) :
    beadMono c a i j * beadMono c a' i' j' = beadMono c (a + a') (i + i') (j + j') := by
  have h01 : Commute (beadCurl0U c) (beadCurl1U c) := Commute.units_of_val (twkOp_commute c).2.2
  have hd0 : Commute (beadTwistU c) (beadCurl0U c) :=
    Commute.units_of_val (twkOp_commute c).2.1
  have hd1 : Commute (beadTwistU c) (beadCurl1U c) := Commute.units_of_val (twkOp_commute c).1
  rw [beadMono, beadMono, beadMono, ← Units.val_mul, zpow_add, zpow_add, zpow_add]
  congr 1
  exact mul_six_comm_beadAlg _ _ _ _ _ _ ((hd1.zpow_zpow a' j).symm).eq
    ((hd0.zpow_zpow a' i).symm).eq ((h01.zpow_zpow i' j).symm).eq

/-! ### Twists, curls and beads as monomials -/

/-- A run of crossings of the band is a tangle on the band. -/
private theorem morseFits_replicate_cross_beadAlg (s : Bool) : ∀ n : ℕ,
    morseFits 2 (List.replicate n (isoX s 0)) = true ∧
      morseOut 2 (List.replicate n (isoX s 0)) = 2
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    have ih := morseFits_replicate_cross_beadAlg s n
    rw [List.replicate_succ, morseFits_cons]
    exact ⟨⟨by simp [isoX, morseKindIn], ih.1⟩, ih.2⟩

/-- A concatenation of two tangles on the band is a tangle on the band. -/
private theorem valid_append_beadAlg {u v : MorseWord}
    (hu : morseFits 2 u = true ∧ morseOut 2 u = 2) (hv : morseFits 2 v = true ∧ morseOut 2 v = 2) :
    morseFits 2 (u ++ v) = true ∧ morseOut 2 (u ++ v) = 2 := by
  rw [morseFits_append, morseOut_append, hu.1, hu.2, hv.1, hv.2]
  exact ⟨rfl, rfl⟩

/-- A run of half twists exchanges the curls on the two strands or keeps them. -/
private theorem beadMono_exchange (c : ℕ) (s : Bool) : ∀ n : ℕ,
    (beadMono c 0 0 1 * twkOp c (List.replicate n (isoX s 0)) =
        twkOp c (List.replicate n (isoX s 0)) * beadMono c 0 0 1 ∧
      beadMono c 0 1 0 * twkOp c (List.replicate n (isoX s 0)) =
        twkOp c (List.replicate n (isoX s 0)) * beadMono c 0 1 0) ∨
    (beadMono c 0 0 1 * twkOp c (List.replicate n (isoX s 0)) =
        twkOp c (List.replicate n (isoX s 0)) * beadMono c 0 1 0 ∧
      beadMono c 0 1 0 * twkOp c (List.replicate n (isoX s 0)) =
        twkOp c (List.replicate n (isoX s 0)) * beadMono c 0 0 1)
  | 0 => Or.inl (by
      rw [List.replicate_zero, twkOp_nil]
      simp)
  | n + 1 => by
    have hx : morseFits 2 [isoX s 0] = true ∧ morseOut 2 [isoX s 0] = 2 := by
      cases s <;> decide
    have hRL : twkOp c (isoCurlR true 1) = twkOp c (isoCurlL true 1) :=
      twkOp_eq_of_morseReach (show MorseReach 2 (isoCurlR true 1) (isoCurlL true 1) from
        (by decide : isoBeadsWord [.p] = isoCurlL true 1) ▸ morseReach_isoPark_RP) c
    have h1 : beadMono c 0 0 1 * twkOp c [isoX s 0] = twkOp c [isoX s 0] * beadMono c 0 1 0 := by
      have h := twkOp_eq_of_morseReach (morseReach_xCurl_beadAlg s) c
      rw [twkOp_append c _ _ hx.1 hx.2, twkOp_append c _ _ (by decide) (by decide), hRL] at h
      rw [beadMono_curl1, beadMono_curl0]
      exact h.symm
    have h0 : beadMono c 0 1 0 * twkOp c [isoX s 0] = twkOp c [isoX s 0] * beadMono c 0 0 1 := by
      have h := twkOp_eq_of_morseReach (morseReach_curlX_beadAlg s) c
      rw [twkOp_append c _ _ (by decide) (by decide), twkOp_append c _ _ hx.1 hx.2, hRL] at h
      rw [beadMono_curl1, beadMono_curl0]
      exact h
    have hT : twkOp c (List.replicate (n + 1) (isoX s 0)) =
        twkOp c [isoX s 0] * twkOp c (List.replicate n (isoX s 0)) := by
      rw [List.replicate_succ, ← twkOp_append c _ _ hx.1 hx.2]
      rfl
    rw [hT]
    rcases beadMono_exchange c s n with ⟨k1, k0⟩ | ⟨k1, k0⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [← mul_assoc, h1, mul_assoc, k0, mul_assoc]
      · rw [← mul_assoc, h0, mul_assoc, k1, mul_assoc]
    · refine Or.inl ⟨?_, ?_⟩
      · rw [← mul_assoc, h1, mul_assoc, k0, mul_assoc]
      · rw [← mul_assoc, h0, mul_assoc, k1, mul_assoc]

/-- The operators of a block `A1` and of a positive curl, as they are or rotated. -/
private theorem twkOp_bead_beadAlg (c : ℕ) (b : MorseWord) :
    (b = phaseTwoA1 ∨ b = isoRot 2 phaseTwoA1 →
      ∃ i j : ℤ, i + j = -1 ∧ twkOp c b = beadMono c 1 i j) ∧
    (b = isoCurlL true 1 ∨ b = isoRot 2 (isoCurlL true 1) →
      ∃ i j : ℤ, i + j = 1 ∧ twkOp c b = beadMono c 0 i j) := by
  refine ⟨?_, ?_⟩
  · rintro (rfl | rfl)
    · refine ⟨0, -1, by norm_num, ?_⟩
      rw [phaseTwoA1_eq_twkTw, twkOp_append c _ _ (by decide) (by decide), ← beadMono_twist,
        ← beadMono_curl1_inv, beadMono_mul]
      norm_num
    · refine ⟨-1, 0, by norm_num, ?_⟩
      rw [isoRot_phaseTwoA1, twkOp_append c _ _ (by decide) (by decide), ← beadMono_twist,
        ← beadMono_curl0_inv, beadMono_mul]
      norm_num
  · rintro (rfl | rfl)
    · exact ⟨0, 1, by norm_num, (beadMono_curl1 c).symm⟩
    · exact ⟨1, 0, by norm_num, by rw [isoRot_isoCurlL_true_one, beadMono_curl0]⟩

/-- The operator of a list of beads, each as it is or rotated: a monomial, or two monomials
around the clasp, with the exponents counted by the beads. -/
private theorem twkOp_beads_beadAlg (c : ℕ) (σ : Bool) : ∀ L' L : List MorseWord,
    List.Forall₂ (fun a b : MorseWord ↦ b = a ∨ b = isoRot 2 a) L' L →
    (∀ x ∈ L', x = phaseTwoA1 ∨ x = isoCurlL true 1 ∨ x = claspSWord σ) →
    (morseFits 2 L.flatten = true ∧ morseOut 2 L.flatten = 2) ∧
    (L'.count (claspSWord σ) = 0 → ∃ i j : ℤ,
      i + j = (L'.count (isoCurlL true 1) : ℤ) - L'.count phaseTwoA1 ∧
        twkOp c L.flatten = beadMono c (L'.count phaseTwoA1) i j) ∧
    (L'.count (claspSWord σ) = 1 → ∃ (a b : ℕ) (i j i' j' : ℤ),
      a + b = L'.count phaseTwoA1 ∧
        i + j + i' + j' = (L'.count (isoCurlL true 1) : ℤ) - L'.count phaseTwoA1 ∧
        twkOp c L.flatten = beadMono c a i j * twkOp c (claspSWord σ) * beadMono c b i' j')
  | _, _, .nil, _ =>
    ⟨⟨rfl, rfl⟩, fun _ ↦ ⟨0, 0, by simp, by simp [twkOp_nil, beadMono_zero]⟩, fun h ↦ by simp at h⟩
  | _, _, @List.Forall₂.cons _ _ _ a' b L'' Lt hab htl, hmem => by
    obtain ⟨hv, ih0, ih1⟩ := twkOp_beads_beadAlg c σ L'' Lt htl
      fun x hx ↦ hmem x (List.mem_cons_of_mem _ hx)
    have hAP : phaseTwoA1 ≠ isoCurlL true 1 := by decide
    have hAC : phaseTwoA1 ≠ claspSWord σ := by cases σ <;> decide
    have hPC : isoCurlL true 1 ≠ claspSWord σ := by cases σ <;> decide
    have hbv : morseFits 2 b = true ∧ morseOut 2 b = 2 := by
      rcases hmem a' List.mem_cons_self with rfl | rfl | rfl <;> rcases hab with rfl | rfl <;>
        first | decide | (cases σ <;> decide)
    have hop : twkOp c (b :: Lt).flatten = twkOp c b * twkOp c Lt.flatten := by
      rw [List.flatten_cons, twkOp_append c b _ hbv.1 hbv.2]
    refine ⟨valid_append_beadAlg hbv hv, ?_⟩
    rcases hmem a' List.mem_cons_self with rfl | rfl | rfl
    · obtain ⟨i₀, j₀, hs, hb⟩ := (twkOp_bead_beadAlg c b).1 hab
      simp only [List.count_cons_self, List.count_cons_of_ne hAP, List.count_cons_of_ne hAC]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · obtain ⟨i, j, hij, hih⟩ := ih0 h
        refine ⟨i₀ + i, j₀ + j, by push_cast; omega, ?_⟩
        rw [hop, hb, hih, beadMono_mul]
        congr 1
        push_cast
        ring
      · obtain ⟨a, b', i, j, i', j', hab', hij, hih⟩ := ih1 h
        refine ⟨a + 1, b', i₀ + i, j₀ + j, i', j', by omega, by push_cast; omega, ?_⟩
        rw [hop, hb, hih, ← mul_assoc, ← mul_assoc, beadMono_mul]
        congr 3
        push_cast
        ring
    · obtain ⟨i₀, j₀, hs, hb⟩ := (twkOp_bead_beadAlg c b).2 hab
      simp only [List.count_cons_self, List.count_cons_of_ne hAP.symm,
        List.count_cons_of_ne hPC]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · obtain ⟨i, j, hij, hih⟩ := ih0 h
        refine ⟨i₀ + i, j₀ + j, by push_cast; omega, ?_⟩
        rw [hop, hb, hih, beadMono_mul, zero_add]
      · obtain ⟨a, b', i, j, i', j', hab', hij, hih⟩ := ih1 h
        refine ⟨a, b', i₀ + i, j₀ + j, i', j', hab', by push_cast; omega, ?_⟩
        rw [hop, hb, hih, ← mul_assoc, ← mul_assoc, beadMono_mul, zero_add]
    · have hK : twkOp c b = twkOp c (claspSWord σ) := by
        rcases hab with rfl | rfl
        · rfl
        · rw [isoRot_claspSWord]
      simp only [List.count_cons_self, List.count_cons_of_ne hAC.symm,
        List.count_cons_of_ne hPC.symm]
      refine ⟨fun h ↦ absurd h (Nat.succ_ne_zero _), fun h ↦ ?_⟩
      obtain ⟨i, j, hij, hih⟩ := ih0 (by omega)
      refine ⟨0, L''.count phaseTwoA1, 0, 0, i, j, by omega, by omega, ?_⟩
      rw [hop, hK, hih, Nat.cast_zero, beadMono_zero, one_mul]

/-- The operator of a run of half twists of the band. -/
private theorem twkOp_twTwistWord_beadAlg (c : ℕ) (k : ℤ) :
    twkOp c (twTwistWord k) = halfTwistZ c k := by
  rw [twkOp, morseOp_twTwistWord c k (2 * c) le_rfl, skPlace_self]

/-- A power of the negative full twist. -/
private theorem beadMono_pow_twist (c : ℕ) : ∀ n : ℕ,
    beadMono c n 0 0 = halfTwistZ c (-2 * n)
  | 0 => by
    rw [Nat.cast_zero, beadMono_zero, mul_zero]
    simp [halfTwistZ]
  | n + 1 => by
    have h := beadMono_mul c n 0 0 1 0 0
    rw [beadMono_pow_twist c n, beadMono_twist,
      show twkTw 1 = twTwistWord (-2) from by decide, twkOp_twTwistWord_beadAlg,
      ← halfTwistZ_add] at h
    rw [show ((n + 1 : ℕ) : ℤ) = n + 1 by push_cast; ring, show (0 : ℤ) = 0 + 0 by ring, ← h]
    congr 1
    ring

/-- The thick operator of an evacuated word: the order of the beads does not matter. -/
theorem morseOp_twkEvacuated (G : MorseWord) (hG : morseFits 1 G = true ∧ morseOut 1 G = 1)
    (hc : IsoConnected G) (σ : Bool) (N : ℕ) (k : ℤ) (L : List MorseWord)
    (hL : IsoRotPerm (List.replicate N phaseTwoA1 ++ List.replicate N (isoCurlL true 1) ++
      [claspSWord σ]) L) (c : ℕ) :
    morseOp c ([isoU 1] ++ twTwistWord k ++ morseDouble G ++ L.flatten ++ [isoN 1]) c c =
      morseOp c ([isoU 1] ++ morseDouble G ++ twTwistWord (k - 2 * (N : ℤ)) ++ claspSWord σ ++
        [isoN 1]) c c := by
  obtain ⟨L', hperm, hf⟩ := hL
  have hAP : phaseTwoA1 ≠ isoCurlL true 1 := by decide
  have hAC : phaseTwoA1 ≠ claspSWord σ := by cases σ <;> decide
  have hPC : isoCurlL true 1 ≠ claspSWord σ := by cases σ <;> decide
  have hmem : ∀ x ∈ L', x = phaseTwoA1 ∨ x = isoCurlL true 1 ∨ x = claspSWord σ := by
    intro x hx
    have h := hperm.subset hx
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at h
    tauto
  have cr : ∀ x y : MorseWord, y ≠ x → (List.replicate N y).count x = 0 := fun x y h ↦
    List.count_eq_zero_of_not_mem fun hm ↦ h (List.eq_of_mem_replicate hm).symm
  have cs : ∀ x y : MorseWord, y ≠ x → [y].count x = 0 := fun x y h ↦
    List.count_eq_zero_of_not_mem fun hm ↦ h (List.mem_singleton.1 hm).symm
  have hcA : L'.count phaseTwoA1 = N := by
    rw [hperm.count_eq, List.count_append, List.count_append, List.count_replicate_self,
      cr _ _ hAP.symm, cs _ _ hAC.symm, Nat.add_zero]
  have hcP : L'.count (isoCurlL true 1) = N := by
    rw [hperm.count_eq, List.count_append, List.count_append, List.count_replicate_self,
      cr _ _ hAP, cs _ _ hPC.symm, Nat.zero_add, Nat.add_zero]
  have hcC : L'.count (claspSWord σ) = 1 := by
    rw [hperm.count_eq, List.count_append, List.count_append, List.count_singleton_self,
      cr _ _ hAC, cr _ _ hPC]
  obtain ⟨hLv, -, h1⟩ := twkOp_beads_beadAlg c σ L' L hf hmem
  obtain ⟨a, b, i, j, i', j', hab, hij, hop⟩ := h1 hcC
  have hD : morseFits 2 (morseDouble G) = true ∧ morseOut 2 (morseDouble G) = 2 := by
    have h := morseFits_isoSlotWord 1 0 G (fun _ _ ↦ []) hG.1 (fun _ _ ↦ ⟨rfl, rfl⟩)
    rwa [isoSlotWord_nil, hG.2] at h
  have hT : ∀ m : ℤ, morseFits 2 (twTwistWord m) = true ∧ morseOut 2 (twTwistWord m) = 2 :=
    fun m ↦ morseFits_replicate_cross_beadAlg _ _
  have hKv : morseFits 2 (claspSWord σ) = true ∧ morseOut 2 (claspSWord σ) = 2 := by
    cases σ <;> decide
  have hW1 := valid_append_beadAlg (valid_append_beadAlg (hT k) hD) hLv
  have hW2 := valid_append_beadAlg (valid_append_beadAlg hD (hT (k - 2 * (N : ℤ)))) hKv
  have hcomm := twkOp_morseDouble_commute G hG hc c
  have key := evac_alg_beadAlg (ptrTail c (2 * c)) (beadMono c) (twkOp c (claspSWord σ))
    (twkOp c (morseDouble G)) (twkOp c (twTwistWord k)) (beadMono_zero c) (beadMono_mul c)
    (by rw [beadMono_curl0, beadMono_curl1]; exact twkOp_curl_clasp σ c)
    (by rw [beadMono_curl0, beadMono_curl1]; exact twkOp_clasp_curl σ c)
    (by
      have e1 : beadMono c 1 (-1) (-1) = twkOp c (twkTw 1) * twkOp c (isoCurlR false 0) *
          twkOp c (isoCurlL false 1) := by
        rw [← beadMono_twist, ← beadMono_curl0_inv, ← beadMono_curl1_inv, beadMono_mul,
          beadMono_mul]
        norm_num
      have e2 : beadMono c 0 1 1 = twkOp c (isoCurlL true 1) * twkOp c (isoCurlR true 0) := by
        rw [← beadMono_curl1, ← beadMono_curl0, beadMono_mul]
        norm_num
      rw [beadMono_twist, e1, e2, twkOp_clasp_twist σ c]
      simp only [mul_assoc])
    (fun M ↦ by rw [beadMono_curl1]; exact ptrTail_twkOp_curl_comm c true M)
    (fun M ↦ by rw [beadMono_curl1_inv]; exact ptrTail_twkOp_curl_comm c false M)
    ((beadMono_exchange c _ k.natAbs).elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1))
    (by rw [beadMono_curl0]; exact hcomm.2.2.eq.symm)
    (by rw [beadMono_curl1]; exact hcomm.2.1.eq.symm)
    ((hcomm.1 k).eq.symm) a b i j i' j' (by omega)
  have hTD : twkOp c (twTwistWord k) * beadMono c ((a : ℤ) + b) 0 0 =
      twkOp c (twTwistWord (k - 2 * (N : ℤ))) := by
    rw [show (a : ℤ) + b = (N : ℕ) by omega, beadMono_pow_twist, twkOp_twTwistWord_beadAlg,
      twkOp_twTwistWord_beadAlg, ← halfTwistZ_add]
    congr 1
  rw [show [isoU 1] ++ twTwistWord k ++ morseDouble G ++ L.flatten ++ [isoN 1] =
      [isoU 1] ++ (twTwistWord k ++ morseDouble G ++ L.flatten) ++ [isoN 1] by
      simp only [List.append_assoc],
    show [isoU 1] ++ morseDouble G ++ twTwistWord (k - 2 * (N : ℤ)) ++ claspSWord σ ++ [isoN 1] =
      [isoU 1] ++ (morseDouble G ++ twTwistWord (k - 2 * (N : ℤ)) ++ claspSWord σ) ++ [isoN 1] by
      simp only [List.append_assoc],
    morseOp_twkBracket c _ hW1.1 hW1.2, morseOp_twkBracket c _ hW2.1 hW2.2,
    twkOp_append c (twTwistWord k ++ morseDouble G) _ (valid_append_beadAlg (hT k) hD).1
      (valid_append_beadAlg (hT k) hD).2,
    twkOp_append c (twTwistWord k) _ (hT k).1 (hT k).2, hop,
    twkOp_append c (morseDouble G ++ twTwistWord (k - 2 * (N : ℤ))) _
      (valid_append_beadAlg hD (hT _)).1 (valid_append_beadAlg hD (hT _)).2,
    twkOp_append c (morseDouble G) _ hD.1 hD.2, ← mul_assoc, ← mul_assoc, key,
    mul_assoc (twkOp c (morseDouble G)), hTD]

/-- The band-and-clasp word over the core of the annulus has the operator of the band-and-clasp
word over the torus braid. -/
theorem morseOp_twkCoreTarget {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) (k : ℤ) (σ : Bool)
    (c : ℕ) :
    morseOp c ([isoU 1] ++ morseDouble (pairCore r s) ++ twTwistWord k ++ claspSWord σ ++
        [isoN 1]) c c = morseOp c (twTargetWord r s k σ) c c := by
  have hf := (morseFits_pairCore h hr).1
  have hd := morseReach_morseDouble (morseReach_pairCore_torus h hr) hf
  have hfD : morseFits 2 (morseDouble (pairCore r s)) = true := by
    have h := morseFits_isoSlotWord 1 0 (pairCore r s) (fun _ _ ↦ []) hf (fun _ _ ↦ ⟨rfl, rfl⟩)
    rw [isoSlotWord_nil] at h
    exact h.1
  have hF := morseReach_frame 2 1 0 1 [isoU 1] (twTwistWord k ++ claspSWord σ ++ [isoN 1]) _ _ hd
    hfD rfl
  rw [morseShiftWord_zero_iso, morseShiftWord_zero_iso] at hF
  obtain ⟨mvs, hm⟩ := hF
  have h2 := morseOp_eq_of_morseApplyAll c 1 c c (Nat.mul_one c).symm _ _ mvs hm
  have e : twTargetWord r s k σ = [isoU 1] ++
      morseDouble (morseLongClosure r (torusPairWord r s)) ++ twTwistWord k ++ claspSWord σ ++
        [isoN 1] := rfl
  rw [e]
  simpa only [List.append_assoc] using h2

end AJConjecture
