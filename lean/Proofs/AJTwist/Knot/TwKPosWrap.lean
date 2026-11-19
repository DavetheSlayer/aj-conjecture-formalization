import Mathlib
import AJTwist.Knot.TwKPosBeadOps
import AJTwist.Knot.TwKPrefix
import AJConjecture.SkeinPtrTailCyclic

/-!
# The closed band: partial trace, the wrap of a curl, and the doubled core

A word `u1 · W · n1` with a tangle `W` on the band `0, 1` (the return strand on the right) has
the operator `ptrTail c (2c) (twkOp c W)`: the partial trace over the second bundle
(`morseOp_twkBracket`; the argument of `morseOp_pairTargetWord`, `ptrTail_eq_cupThick_capThick`).

* `ptrTail_twkOp_curl_comm`: under this partial trace a curl on the second strand at the top end
  of the band is a curl on the second strand at the bottom end, for any operator between them:
  the curl slides over the last cap, down the return strand and around the first cup. Proof:
  `ptrTail_eq_cupThick_capThick`, a curl turns at a thick cap and at a thick cup (operator form
  of the library macros `morseReach_isoPark_capP`, `…capN`, `…cupP`, `…cupN`), and operators
  placed on disjoint bundles commute.
* `twkOp_morseDouble_commute`: the doubled connected long knot commutes with the twists of the
  band and with the curls on its two edges: the journey of a bead from the bottom end to the top
  end (`morseReach_isoBandBead_journey` with the beads `twTwistWord k`, `isoCurlL true 1`,
  `isoCurlR true 0`; a long knot has an even number of cups and caps, so the bead arrives
  unrotated) and `twkOp_eq_of_morseReach`.

Checked outside Lean (`SCR/KP/tools/alg_test.py`): the wrap identity for six tangles, both curl
signs, thickness one and two.
-/

noncomputable section

namespace AJConjecture

/-- The operator of a word that begins with a cup, with free sizes. -/
private theorem morseOp_cons_cup_wrap (c i : ℕ) (u : MorseWord) (N M N' : ℕ)
    (hM : M = N + 2 * c) :
    morseOp c ((MorseKind.cup, i) :: u) N N' =
      skPlace N M (c * i) (cupThick c) * morseOp c u M N' := by
  have e : N + c * 2 - c * 0 = M := by rw [hM]; ring_nf; omega
  rw [← e]
  rfl

/-- The operator of a word that begins with a cap, with free sizes. -/
private theorem morseOp_cons_cap_wrap (c i : ℕ) (u : MorseWord) (N M N' : ℕ)
    (hN : N = M + 2 * c) :
    morseOp c ((MorseKind.cap, i) :: u) N N' =
      skPlace N M (c * i) (capThick c) * morseOp c u M N' := by
  have e : N + c * 0 - c * 2 = M := by rw [hN]; ring_nf; omega
  rw [← e]
  rfl

/-- The operator of a word that begins with a crossing, with free sizes. -/
private theorem morseOp_cons_cross_wrap (c i : ℕ) (s : Bool) (u : MorseWord) (N M N' : ℕ)
    (hM : M = N) :
    morseOp c ((MorseKind.cross s, i) :: u) N N' =
      skPlace N M (c * i) (halfTwist c s) * morseOp c u M N' := by
  have e : N + c * 2 - c * 2 = M := by omega
  rw [← e]
  rfl

/-- A placed letter, placed again at `0` with `e` extra factors on the right. -/
private theorem skPlace_zero_mul_wrap {k l : ℕ} (N M O e j : ℕ) (A : SkMat k l)
    (B : SkMat M O) (hj : j + k ≤ N) (hkl : N + l = M + k) :
    skPlace (N + e) (M + e) j A * skPlace (M + e) (O + e) 0 B =
      skPlace (N + e) (O + e) 0 (skPlace N M j A * B) := by
  rw [skPlace_mul (N + e) (M + e) (O + e) 0 _ B (by omega) (by omega) (by omega),
    skPlace_skPlace (N + e) (M + e) 0 j A hj hkl (by omega) (by omega), Nat.zero_add]

/-- Extra tensor factors on the right of a word that fits pass through its operator. -/
private theorem morseOp_add_right_wrap (d e n : ℕ) (u : MorseWord)
    (hu : morseFits n u = true) :
    morseOp d u (d * n + e) (d * morseOut n u + e) =
      skPlace (d * n + e) (d * morseOut n u + e) 0 (morseOp d u (d * n) (d * morseOut n u)) := by
  induction u generalizing n with
  | nil =>
    change morseOp d [] (d * n + e) (d * n + e) =
      skPlace (d * n + e) (d * n + e) 0 (morseOp d [] (d * n) (d * n))
    rw [morseOp_nil, morseOp_nil, skPlace_one _ 0 _ (by omega)]
  | cons l u ih =>
    obtain ⟨k, i⟩ := l
    simp only [morseFits, Bool.and_eq_true, decide_eq_true_eq] at hu
    obtain ⟨hi, hu⟩ := hu
    have hdi : d * i ≤ d * n := Nat.mul_le_mul_left d (by omega)
    cases k with
    | cup =>
      have hu' : morseFits (n + 2) u = true := by
        simpa [morseLetterOut, morseKindOut, morseKindIn] using hu
      change morseOp d ((MorseKind.cup, i) :: u) (d * n + e) (d * morseOut (n + 2 - 0) u + e) =
        skPlace (d * n + e) (d * morseOut (n + 2 - 0) u + e) 0
          (morseOp d ((MorseKind.cup, i) :: u) (d * n) (d * morseOut (n + 2 - 0) u))
      have hn2 : d * (n + 2) = d * n + 2 * d := by ring
      rw [Nat.sub_zero, morseOp_cons_cup_wrap d i u _ (d * (n + 2) + e) _ (by omega),
        morseOp_cons_cup_wrap d i u _ (d * (n + 2)) _ hn2, ih (n + 2) hu',
        skPlace_zero_mul_wrap _ _ _ e _ _ _ (by omega) (by omega)]
    | cap =>
      simp only [morseKindIn] at hi
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have hu' : morseFits m u = true := by
        simpa [morseLetterOut, morseKindOut, morseKindIn] using hu
      change morseOp d ((MorseKind.cap, i) :: u) (d * (m + 2) + e)
          (d * morseOut (m + 2 + 0 - 2) u + e) =
        skPlace (d * (m + 2) + e) (d * morseOut (m + 2 + 0 - 2) u + e) 0
          (morseOp d ((MorseKind.cap, i) :: u) (d * (m + 2)) (d * morseOut (m + 2 + 0 - 2) u))
      have hn2 : d * (m + 2) = d * m + 2 * d := by ring
      have hdi' : d * i ≤ d * m := Nat.mul_le_mul_left d (by omega)
      rw [show m + 2 + 0 - 2 = m by omega,
        morseOp_cons_cap_wrap d i u _ (d * m + e) _ (by omega),
        morseOp_cons_cap_wrap d i u _ (d * m) _ hn2, ih m hu', hn2,
        skPlace_zero_mul_wrap _ _ _ e _ _ _ (by omega) (by omega)]
    | cross s =>
      simp only [morseKindIn] at hi
      have hu' : morseFits n u = true := by
        simpa [morseLetterOut, morseKindOut, morseKindIn] using hu
      change morseOp d ((MorseKind.cross s, i) :: u) (d * n + e)
          (d * morseOut (n + 2 - 2) u + e) =
        skPlace (d * n + e) (d * morseOut (n + 2 - 2) u + e) 0
          (morseOp d ((MorseKind.cross s, i) :: u) (d * n) (d * morseOut (n + 2 - 2) u))
      have hdi' : d * (i + 2) ≤ d * n := Nat.mul_le_mul_left d (by omega)
      rw [Nat.mul_add] at hdi'
      rw [Nat.add_sub_cancel, morseOp_cons_cross_wrap d i s u _ _ _ rfl,
        morseOp_cons_cross_wrap d i s u _ _ _ rfl, ih n hu',
        skPlace_zero_mul_wrap _ _ _ e _ _ _ (by omega) (by omega)]


/-- The partial trace over the second of two bundles, with free sizes. -/
private theorem ptrTail_eq_cupThick_capThick_wrap (c N M : ℕ) (hN : N = c + c)
    (hM : M = c + 2 * c) (A : SkMat N N) :
    ptrTail c N A =
      skPlace c M c (cupThick c) * skPlace M M 0 A * skPlace M c c (capThick c) := by
  subst hN hM
  exact ptrTail_eq_cupThick_capThick c c A


/-- A tangle on the band with a third bundle on its right. -/
private theorem morseOp_band_three_wrap (c N N' : ℕ) (hN : N = 2 * c) (hN' : N' = 3 * c)
    (W : MorseWord) (hW : morseFits 2 W = true) (hWo : morseOut 2 W = 2) :
    morseOp c W N' N' = skPlace N' N' 0 (morseOp c W N N) := by
  have h := morseOp_add_right_wrap c c 2 W hW
  rw [hWo] at h
  obtain rfl : N = c * 2 := by omega
  obtain rfl : N' = c * 2 + c := by omega
  exact h

/-- The operator of a concatenation, with a free middle size. -/
private theorem morseOp_append_wrap (c : ℕ) (u v : MorseWord) (N M N' : ℕ)
    (hM : M = morseThickOut c N u) :
    morseOp c (u ++ v) N N' = morseOp c u N M * morseOp c v M N' := by
  subst hM
  exact morseOp_append c u v N N'

/-- The cup of the return strand. -/
private theorem morseOp_cup_one_wrap (c : ℕ) :
    morseOp c [(MorseKind.cup, 1)] c (3 * c) = skPlace c (3 * c) c (cupThick c) := by
  rw [morseOp_cons_cup_wrap c 1 [] c (3 * c) (3 * c) (by omega), morseOp_nil, Matrix.mul_one,
    Nat.mul_one]

/-- The cap of the return strand. -/
private theorem morseOp_cap_one_wrap (c : ℕ) :
    morseOp c [(MorseKind.cap, 1)] (3 * c) c = skPlace (3 * c) c c (capThick c) := by
  rw [morseOp_cons_cap_wrap c 1 [] (3 * c) c c (by omega), morseOp_nil, Matrix.mul_one,
    Nat.mul_one]

/-- A tangle on the band keeps the three bundles. -/
private theorem morseThickOut_band_wrap (c : ℕ) (W : MorseWord) (hW : morseFits 2 W = true)
    (hWo : morseOut 2 W = 2) : 3 * c = morseThickOut c (3 * c) W := by
  rw [Nat.mul_comm 3 c, morseThickOut_eq c 3 W (morseFits_add_right_iso 2 1 W hW),
    morseOut_add_right 2 1 W hW, hWo]

/-- The operator of the closed band `u1 · W · n1` is the partial trace over the second bundle. -/
theorem morseOp_twkBracket (c : ℕ) (W : MorseWord) (hW : morseFits 2 W = true)
    (hWo : morseOut 2 W = 2) :
    morseOp c ([isoU 1] ++ W ++ [isoN 1]) c c = ptrTail c (2 * c) (twkOp c W) := by
  have hw : [isoU 1] ++ W ++ [isoN 1] =
      [(MorseKind.cup, 1)] ++ (W ++ [(MorseKind.cap, 1)]) := by
    simp [isoU, isoN]
  have h₁ : 3 * c = morseThickOut c c [(MorseKind.cup, 1)] := by
    simp only [morseThickOut, morseKindOut, morseKindIn]
    omega
  rw [hw, morseOp_append_wrap c _ _ c (3 * c) c h₁,
    morseOp_append_wrap c W _ (3 * c) (3 * c) c (morseThickOut_band_wrap c W hW hWo),
    morseOp_cup_one_wrap, morseOp_cap_one_wrap,
    morseOp_band_three_wrap c (2 * c) (3 * c) rfl rfl W hW hWo,
    ptrTail_eq_cupThick_capThick_wrap c (2 * c) (3 * c) (by omega) (by omega), Matrix.mul_assoc]
  rfl

/-- The curl on the third bundle commutes with operators on the first two bundles. -/
private theorem curl_three_comm_wrap (c : ℕ) (b : Bool) (M : SkMat (2 * c) (2 * c)) :
    skPlace (3 * c) (3 * c) 0 M * morseOp c (isoCurlR b 2) (3 * c) (3 * c) =
      morseOp c (isoCurlR b 2) (3 * c) (3 * c) * skPlace (3 * c) (3 * c) 0 M := by
  have hR : morseOp c (isoCurlR b 2) (3 * c) (3 * c) =
      skPlace (3 * c) (5 * c) (c * 3) (cupThick c) *
        (skPlace (5 * c) (5 * c) (c * 2) (halfTwist c b) *
          skPlace (5 * c) (3 * c) (c * 3) (capThick c)) := by
    rw [isoCurlR, isoU, isoX, isoN, morseOp_cons_cup_wrap c 3 _ (3 * c) (5 * c) _ (by omega),
      morseOp_cons_cross_wrap c 2 b _ (5 * c) (5 * c) _ rfl,
      morseOp_cons_cap_wrap c 3 [] (5 * c) (3 * c) _ (by omega), morseOp_nil, Matrix.mul_one]
  have h1 := skPlace_mul_skPlace_comm (3 * c) (3 * c) (5 * c) (5 * c) 0 (c * 3) M (cupThick c)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have h2 := skPlace_mul_skPlace_comm (5 * c) (5 * c) (5 * c) (5 * c) 0 (c * 2) M
    (halfTwist c b) (by omega) (by omega) (by omega) (by omega) (by omega)
  have h3 := skPlace_mul_skPlace_comm (5 * c) (5 * c) (3 * c) (3 * c) 0 (c * 3) M (capThick c)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [Nat.add_sub_cancel] at h1 h2 h3
  rw [hR, ← Matrix.mul_assoc, h1, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (skPlace _ _ _ _),
    h2, Matrix.mul_assoc, h3]
  simp only [Matrix.mul_assoc]

/-- A curl on the second strand turns at the last cap to the return strand. -/
private theorem morseReach_curlCap_wrap (b : Bool) :
    MorseReach 3 (isoCurlL b 1 ++ [isoN 1]) (isoCurlR b 2 ++ [isoN 1]) := by
  cases b
  · exact morseReach_isoPark_capN
  · exact morseReach_isoPark_capP

/-- A curl on the return strand turns at the first cup to the second strand. -/
private theorem morseReach_cupCurl_wrap (b : Bool) :
    MorseReach 1 ([isoU 1] ++ isoCurlR b 2) ([isoU 1] ++ isoCurlL b 1) := by
  cases b
  · exact morseReach_isoPark_cupN
  · exact morseReach_isoPark_cupP

/-- Under the partial trace a curl on the second strand passes from the top end of the band to
its bottom end. -/
theorem ptrTail_twkOp_curl_comm (c : ℕ) (b : Bool) (M : SkMat (2 * c) (2 * c)) :
    ptrTail c (2 * c) (M * twkOp c (isoCurlL b 1)) =
      ptrTail c (2 * c) (twkOp c (isoCurlL b 1) * M) := by
  have hC : morseFits 2 (isoCurlL b 1) = true ∧ morseOut 2 (isoCurlL b 1) = 2 := by
    cases b <;> decide
  have hR3 : 3 * c = morseThickOut c (3 * c) (isoCurlR b 2) := by
    rw [Nat.mul_comm 3 c, morseThickOut_eq c 3 _ (by cases b <;> decide)]
    cases b <;> rfl
  have hC₁ : morseOp c (isoCurlL b 1) (3 * c) (3 * c) =
      skPlace (3 * c) (3 * c) 0 (twkOp c (isoCurlL b 1)) :=
    morseOp_band_three_wrap c (2 * c) (3 * c) rfl rfl _ hC.1 hC.2
  have hcap : skPlace (3 * c) (3 * c) 0 (twkOp c (isoCurlL b 1)) *
      skPlace (3 * c) c c (capThick c) =
      morseOp c (isoCurlR b 2) (3 * c) (3 * c) * skPlace (3 * c) c c (capThick c) := by
    obtain ⟨mvs, hm⟩ := morseReach_curlCap_wrap b
    have h := morseOp_eq_of_morseApplyAll c 3 (3 * c) c (Nat.mul_comm 3 c) _ _ mvs hm
    rwa [show [isoN 1] = [(MorseKind.cap, 1)] from rfl,
      morseOp_append_wrap c _ _ (3 * c) (3 * c) c (morseThickOut_band_wrap c _ hC.1 hC.2),
      morseOp_append_wrap c _ _ (3 * c) (3 * c) c hR3, morseOp_cap_one_wrap, hC₁] at h
  have hcup : skPlace c (3 * c) c (cupThick c) * morseOp c (isoCurlR b 2) (3 * c) (3 * c) =
      skPlace c (3 * c) c (cupThick c) *
        skPlace (3 * c) (3 * c) 0 (twkOp c (isoCurlL b 1)) := by
    obtain ⟨mvs, hm⟩ := morseReach_cupCurl_wrap b
    have h₁ : 3 * c = morseThickOut c c [(MorseKind.cup, 1)] := by
      simp only [morseThickOut, morseKindOut, morseKindIn]
      omega
    have h := morseOp_eq_of_morseApplyAll c 1 c (3 * c) (Nat.mul_one c).symm _ _ mvs hm
    rwa [show [isoU 1] = [(MorseKind.cup, 1)] from rfl,
      morseOp_append_wrap c _ _ c (3 * c) (3 * c) h₁,
      morseOp_append_wrap c _ _ c (3 * c) (3 * c) h₁, morseOp_cup_one_wrap, hC₁] at h
  have hcomm := curl_three_comm_wrap c b M
  rw [ptrTail_eq_cupThick_capThick_wrap c (2 * c) (3 * c) (by omega) (by omega),
    ptrTail_eq_cupThick_capThick_wrap c (2 * c) (3 * c) (by omega) (by omega),
    skPlace_mul (3 * c) (3 * c) (3 * c) 0 M _ (by omega) (by omega) (by omega),
    skPlace_mul (3 * c) (3 * c) (3 * c) 0 _ M (by omega) (by omega) (by omega)]
  calc skPlace c (3 * c) c (cupThick c) * (skPlace (3 * c) (3 * c) 0 M *
        skPlace (3 * c) (3 * c) 0 (twkOp c (isoCurlL b 1))) * skPlace (3 * c) c c (capThick c)
      = skPlace c (3 * c) c (cupThick c) * (skPlace (3 * c) (3 * c) 0 M *
        (skPlace (3 * c) (3 * c) 0 (twkOp c (isoCurlL b 1)) *
          skPlace (3 * c) c c (capThick c))) := by
        simp only [Matrix.mul_assoc]
    _ = skPlace c (3 * c) c (cupThick c) * (skPlace (3 * c) (3 * c) 0 M *
        morseOp c (isoCurlR b 2) (3 * c) (3 * c)) * skPlace (3 * c) c c (capThick c) := by
        rw [hcap]
        simp only [Matrix.mul_assoc]
    _ = skPlace c (3 * c) c (cupThick c) * morseOp c (isoCurlR b 2) (3 * c) (3 * c) *
        skPlace (3 * c) (3 * c) 0 M * skPlace (3 * c) c c (capThick c) := by
        rw [hcomm]
        simp only [Matrix.mul_assoc]
    _ = skPlace c (3 * c) c (cupThick c) * (skPlace (3 * c) (3 * c) 0
        (twkOp c (isoCurlL b 1)) * skPlace (3 * c) (3 * c) 0 M) *
          skPlace (3 * c) c c (capThick c) := by
        rw [hcup]
        simp only [Matrix.mul_assoc]

/-- The number of turns of a word, letter by letter. -/
private theorem isoTurns_cons_wrap (l : MorseLetter) (w : MorseWord) :
    isoTurns (l :: w) = (match l.1 with
      | .cross _ => 0
      | _ => 1) + isoTurns w := by
  obtain ⟨k, i⟩ := l
  cases k <;> simp [isoTurns] <;> omega

/-- Cups and caps change the number of strands by two each. -/
private theorem morseOut_isoTurns_wrap : ∀ (w : MorseWord) (n : ℕ), morseFits n w = true →
    ∃ c, morseOut n w + 4 * c = n + 2 * isoTurns w
  | [], n, _ => ⟨0, by simp [isoTurns, morseOut]⟩
  | l :: w, n, h => by
    rw [morseFits_cons] at h
    obtain ⟨c, hc⟩ := morseOut_isoTurns_wrap w (morseLetterOut n l) h.2
    obtain ⟨k, i⟩ := l
    rw [isoTurns_cons_wrap]
    cases k with
    | cup =>
      refine ⟨c, ?_⟩
      simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut] at hc h ⊢
      omega
    | cap =>
      refine ⟨c + 1, ?_⟩
      simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut] at hc h ⊢
      omega
    | cross s =>
      refine ⟨c, ?_⟩
      simp only [morseOut, morseLetterOut, morseKindIn, morseKindOut] at hc h ⊢
      omega

/-- A run of crossings of the band is a tangle on the band. -/
private theorem morseFits_replicate_cross_wrap (s : Bool) : ∀ n : ℕ,
    morseFits 2 (List.replicate n (isoX s 0)) = true ∧
      morseOut 2 (List.replicate n (isoX s 0)) = 2
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    have ih := morseFits_replicate_cross_wrap s n
    rw [List.replicate_succ, morseFits_cons]
    exact ⟨⟨by simp [isoX, morseKindIn], ih.1⟩, ih.2⟩

/-- The doubled connected long knot commutes with the twists of the band and with the curls on
its two edges. -/
theorem twkOp_morseDouble_commute (G : MorseWord)
    (hG : morseFits 1 G = true ∧ morseOut 1 G = 1) (hc : IsoConnected G) (c : ℕ) :
    (∀ k : ℤ, Commute (twkOp c (morseDouble G)) (twkOp c (twTwistWord k))) ∧
      Commute (twkOp c (morseDouble G)) (twkOp c (isoCurlL true 1)) ∧
      Commute (twkOp c (morseDouble G)) (twkOp c (isoCurlR true 0)) := by
  have hEven : Even (isoTurns G) := by
    obtain ⟨c, hc⟩ := morseOut_isoTurns_wrap G 1 hG.1
    rw [hG.2] at hc
    exact ⟨c, by omega⟩
  have hD : morseFits 2 (morseDouble G) = true ∧ morseOut 2 (morseDouble G) = 2 := by
    have h := morseFits_isoSlotWord 1 0 G (fun _ _ ↦ []) hG.1 (fun _ _ ↦ ⟨rfl, rfl⟩)
    rwa [isoSlotWord_nil, hG.2] at h
  have key : ∀ T : MorseWord, morseFits 2 T = true ∧ morseOut 2 T = 2 →
      Commute (twkOp c (morseDouble G)) (twkOp c T) := by
    intro T hT
    have h := morseReach_isoBandBead_journey G T [] [] 2 0 hG hc hT rfl
    simp only [hEven, ite_true, List.nil_append, List.append_nil] at h
    have h2 := twkOp_eq_of_morseReach h c
    rw [twkOp_append c T _ hT.1 hT.2, twkOp_append c _ T hD.1 hD.2] at h2
    exact h2.symm
  exact ⟨fun k ↦ key _ (morseFits_replicate_cross_wrap _ _), key _ (by decide),
    key _ (by decide)⟩

end AJConjecture
