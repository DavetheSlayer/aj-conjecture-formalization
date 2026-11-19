import Mathlib
import AJTwist.Knot.TwKPosMacros
import AJTwist.Knot.TwKPosEvacDefs
import AJConjecture.SkeinMorseCheckSound
import AJHandoff.TorusKnot.PairKIsoParkCross
import AJHandoff.TorusKnot.PairKIsoParkClasp
import AJHandoff.TorusKnot.PairKIsoParkMacros
import AJHandoff.TorusKnot.PairKIsoParkMacrosL

/-!
# The thick operators of the beads

`twkOp c w` is the operator at thickness `c` of a tangle `w` on the band (two bundles of `c`
strands). Isotopic tangles have the same operator (`twkOp_eq_of_morseReach`, soundness of the
checker), and the operator of a concatenation is the product (`twkOp_append`). With

* `D = twkOp c (twkTw 1)` (the negative full twist of the band),
* `P₁, Q₁ = twkOp c (isoCurlL true 1), twkOp c (isoCurlL false 1)` (curls on the second strand),
* `P₀, Q₀ = twkOp c (isoCurlR true 0), twkOp c (isoCurlR false 0)` (curls on the first strand),
* `K = twkOp c (claspSWord σ)` (the clasp of sign `σ`),

the facts used by the evaluation of an evacuated word (`TwKPosBeadAlg`) are:

1. `P₁ Q₁ = Q₁ P₁ = P₀ Q₀ = Q₀ P₀ = 1`, and `D, P₀, P₁` commute pairwise
   (`twkOp_curl_inv`, `twkOp_commute`): library macros `morseReach_isoPark_PN`, `…NP`,
   `…LNLP`, `…TP`, `…LPT`, `…LPP` (the bead words are `isoBeadWord .p = isoCurlL true 1`, `.n`,
   `.lp = isoCurlR true 0`, `.ln`, `.t = twkTw 1`);
2. the beads: `phaseTwoA1 = twkTw 1 ++ isoCurlL false 1`, and the rotations
   `isoRot 2 phaseTwoA1 = isoCurlR false 0 ++ twkTw 1`,
   `isoRot 2 (isoCurlL true 1) = isoCurlR true 0`, `isoRot 2 (claspSWord σ) = claspSWord σ`
   (equalities of words, by `decide`);
3. at the clasp a curl changes the edge, below and above: `P₀ K = P₁ K`, `K P₀ = K P₁`
   (`twkOp_curl_clasp`, `twkOp_clasp_curl`). For `σ = true` from the library macros
   `morseReach_isoPark_LPCS`, `…CSLP` (stated for the conjugated clasp
   `isoClaspU = +0 · claspWord · −0`) and the passage of a curl through one crossing; for
   `σ = false` by small macros: a curl passes a crossing (six to eight moves, found), turns at
   a cap or a cup (four and five moves, found; `SCR/KP/tools/srch9.py`);
4. a twist passes the clasp with curls: `K D = D Q₀ Q₁ K P₁ P₀` (`twkOp_clasp_twist`), for any
   tangle in place of the clasp: `morseReach_isoPark_twistDcurl` (a twist is a doubled curl and
   two edge curls) and `morseReach_isoBead_dcurl` (any band bead passes a doubled curl).

All relations were checked outside Lean at thickness one, two and three
(`SCR/KP/tools/beadops_test.py`), both clasp signs.
-/

noncomputable section

namespace AJConjecture

/-- The thick operator of a tangle on the band at thickness `c`. -/
def twkOp (c : ℕ) (w : MorseWord) : SkMat (2 * c) (2 * c) := morseOp c w (2 * c) (2 * c)

/-- Isotopic tangles on the band have the same thick operator. -/
theorem twkOp_eq_of_morseReach {w w' : MorseWord} (h : MorseReach 2 w w') (c : ℕ) :
    twkOp c w = twkOp c w' := by
  obtain ⟨mvs, hm⟩ := h
  exact morseOp_eq_of_morseApplyAll c 2 (2 * c) (2 * c) (Nat.mul_comm 2 c) w w' mvs hm

/-- The thick operator of a concatenation of tangles on the band. -/
theorem twkOp_append (c : ℕ) (u v : MorseWord) (hu : morseFits 2 u = true)
    (huo : morseOut 2 u = 2) : twkOp c (u ++ v) = twkOp c u * twkOp c v := by
  have hM : morseThickOut c (2 * c) u = 2 * c := by
    rw [Nat.mul_comm 2 c, morseThickOut_eq c 2 u hu, huo]
  unfold twkOp
  rw [morseOp_append, hM]

/-- The thick operator of the empty tangle. -/
theorem twkOp_nil (c : ℕ) : twkOp c [] = 1 := morseOp_nil c (2 * c)

/-- The rotations of the beads. -/
theorem isoRot_phaseTwoA1 : isoRot 2 phaseTwoA1 = isoCurlR false 0 ++ twkTw 1 := by decide

theorem isoRot_isoCurlL_true_one : isoRot 2 (isoCurlL true 1) = isoCurlR true 0 := by decide

theorem isoRot_claspSWord (σ : Bool) : isoRot 2 (claspSWord σ) = claspSWord σ := by
  cases σ <;> decide

theorem phaseTwoA1_eq_twkTw : phaseTwoA1 = twkTw 1 ++ isoCurlL false 1 := by decide

/-- Isotopic concatenations of two tangles on the band: the products of the operators agree. -/
private theorem twkOp_mul_eq_of_reach_beadOps {a b a' b' : MorseWord}
    (h : MorseReach 2 (a ++ b) (a' ++ b')) (ha : morseFits 2 a = true ∧ morseOut 2 a = 2)
    (ha' : morseFits 2 a' = true ∧ morseOut 2 a' = 2) (c : ℕ) :
    twkOp c a * twkOp c b = twkOp c a' * twkOp c b' := by
  rw [← twkOp_append c a b ha.1 ha.2, ← twkOp_append c a' b' ha'.1 ha'.2]
  exact twkOp_eq_of_morseReach h c

/-- A concatenation of two tangles on the band that is isotopic to the empty tangle. -/
private theorem twkOp_mul_eq_one_of_reach_beadOps {a b : MorseWord}
    (h : MorseReach 2 (a ++ b) []) (ha : morseFits 2 a = true ∧ morseOut 2 a = 2) (c : ℕ) :
    twkOp c a * twkOp c b = 1 := by
  rw [← twkOp_append c a b ha.1 ha.2, twkOp_eq_of_morseReach h c, twkOp_nil]

/-- Reachability between words given up to equality. -/
private theorem morseReach_cast_beadOps {n : ℕ} {a b a' b' : MorseWord} (h : MorseReach n a b)
    (ha : a' = a) (hb : b' = b) : MorseReach n a' b' := ha ▸ hb ▸ h

/-- A positive right curl on the first strand passes a crossing to the second strand. -/
private theorem morseReach_curlX_beadOps (s : Bool) :
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
private theorem morseReach_xCurl_beadOps (s : Bool) :
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

/-- A positive curl turns at a cap. -/
private theorem morseReach_curlCap_beadOps :
    MorseReach 2 (isoCurlR true 0 ++ [isoN 0]) (isoCurlL true 1 ++ [isoN 0]) :=
  ⟨[(2, .capSlide 1 true false, true), (4, .exch (.cap, 0) (.cap, 2), true),
    (1, .exch (.cross true, 0) (.cross true, 2), false), (2, .capSlide 0 true true, false)],
    by decide⟩

/-- A positive curl turns at a cup. -/
private theorem morseReach_cupCurl_beadOps :
    MorseReach 0 ([isoU 0] ++ isoCurlR true 0) ([isoU 0] ++ isoCurlL true 1) :=
  ⟨[(1, .cupSlide 0 false false, true), (0, .exch (.cup, 0) (.cup, 0), true),
    (1, .cupSlide 1 true false, true), (3, .r2 1 true, false), (3, .r2 0 false, false)],
    by decide⟩

/-- On the second strand a positive right curl is a positive left curl. -/
private theorem morseReach_curlRL_beadOps :
    MorseReach 2 (isoCurlR true 1) (isoCurlL true 1) :=
  morseReach_cast_beadOps morseReach_isoPark_RP rfl (by decide)

/-- Below the clasp a positive curl on the first strand slides over the cap and through the two
crossings to the second strand. -/
private theorem morseReach_curl_clasp_beadOps (s : Bool) :
    MorseReach 2 (isoCurlR true 0 ++ claspSWord s) (isoCurlL true 1 ++ claspSWord s) := by
  have h01 : MorseReach 2 (isoCurlR true 0 ++ claspSWord s)
      ([isoU 2, isoX s 1, isoX s 1] ++ isoCurlR true 0 ++ [isoN 0]) :=
    morseReach_cast_beadOps (morseReach_isoBead_commR 2 0 1 (isoCurlR true 0) []
      [isoU 2, isoX s 1, isoX s 1] [isoN 0] (by decide) (by decide) (by cases s <;> decide)
      (by cases s <;> rfl) (by decide)) (by cases s <;> rfl) (by cases s <;> rfl)
  have h12 : MorseReach 2 ([isoU 2, isoX s 1, isoX s 1] ++ isoCurlR true 0 ++ [isoN 0])
      ([isoU 2, isoX s 1, isoX s 1] ++ isoCurlL true 1 ++ [isoN 0]) :=
    morseReach_cast_beadOps (morseReach_frame 2 2 0 2 [isoU 2, isoX s 1, isoX s 1] [] _ _
      morseReach_curlCap_beadOps (by decide) (by cases s <;> rfl)) (by cases s <;> rfl)
      (by cases s <;> rfl)
  have h23 : MorseReach 2 ([isoU 2, isoX s 1, isoX s 1] ++ isoCurlL true 1 ++ [isoN 0])
      ([isoU 2, isoX s 1, isoX s 1] ++ isoCurlR true 1 ++ [isoN 0]) :=
    morseReach_cast_beadOps (morseReach_frame 2 2 0 2 [isoU 2, isoX s 1, isoX s 1] [isoN 0] _ _
      (morseReach_symm morseReach_curlRL_beadOps) (by decide) (by cases s <;> rfl))
      (by cases s <;> rfl) (by cases s <;> rfl)
  have h34 : MorseReach 2 ([isoU 2, isoX s 1, isoX s 1] ++ isoCurlR true 1 ++ [isoN 0])
      ([isoU 2, isoX s 1] ++ isoCurlR true 2 ++ [isoX s 1, isoN 0]) :=
    morseReach_cast_beadOps (morseReach_frame 2 2 1 1 [isoU 2, isoX s 1] [isoN 0] _ _
      (morseReach_xCurl_beadOps s) (by cases s <;> decide) (by cases s <;> rfl))
      (by cases s <;> rfl) (by cases s <;> rfl)
  have h45 : MorseReach 2 ([isoU 2, isoX s 1] ++ isoCurlR true 2 ++ [isoX s 1, isoN 0])
      ([isoU 2] ++ isoCurlR true 1 ++ [isoX s 1, isoX s 1, isoN 0]) :=
    morseReach_cast_beadOps (morseReach_frame 2 2 1 1 [isoU 2] [isoX s 1, isoN 0] _ _
      (morseReach_symm (morseReach_curlX_beadOps s)) (by cases s <;> decide) (by decide))
      (by cases s <;> rfl) (by cases s <;> rfl)
  have h56 : MorseReach 2 ([isoU 2] ++ isoCurlR true 1 ++ [isoX s 1, isoX s 1, isoN 0])
      (isoCurlR true 1 ++ claspSWord s) :=
    morseReach_cast_beadOps (morseReach_symm (morseReach_isoBead_commR 2 0 2 (isoCurlR true 1)
      [] [isoU 2] [isoX s 1, isoX s 1, isoN 0] (by decide) (by decide) (by decide) (by decide)
      (by decide))) (by cases s <;> rfl) (by cases s <;> rfl)
  have h67 : MorseReach 2 (isoCurlR true 1 ++ claspSWord s) (isoCurlL true 1 ++ claspSWord s) :=
    morseReach_cast_beadOps (morseReach_frame 2 2 0 0 [] (claspSWord s) _ _
      morseReach_curlRL_beadOps (by decide) (by decide)) (by cases s <;> rfl)
      (by cases s <;> rfl)
  exact morseReach_trans h01 (morseReach_trans h12 (morseReach_trans h23 (morseReach_trans h34
    (morseReach_trans h45 (morseReach_trans h56 h67)))))

/-- Above the clasp a positive curl on the first strand slides through the two crossings and
around the cup to the second strand. -/
private theorem morseReach_clasp_curl_beadOps (s : Bool) :
    MorseReach 2 (claspSWord s ++ isoCurlR true 0) (claspSWord s ++ isoCurlL true 1) := by
  have g01 : MorseReach 2 (claspSWord s ++ isoCurlR true 0)
      ([isoU 2, isoX s 1, isoX s 1] ++ isoCurlR true 2 ++ [isoN 0]) :=
    morseReach_cast_beadOps (morseReach_symm (morseReach_isoShiftComm 2 2 1 1
      [isoU 2, isoX s 1, isoX s 1] [isoN 0] (isoCurlR true 0) [] (by decide) (by decide)
      (by cases s <;> rfl))) (by cases s <;> rfl) (by cases s <;> rfl)
  have g12 : MorseReach 2 ([isoU 2, isoX s 1, isoX s 1] ++ isoCurlR true 2 ++ [isoN 0])
      ([isoU 2, isoX s 1] ++ isoCurlR true 1 ++ [isoX s 1, isoN 0]) :=
    morseReach_cast_beadOps (morseReach_frame 2 2 1 1 [isoU 2, isoX s 1] [isoN 0] _ _
      (morseReach_symm (morseReach_curlX_beadOps s)) (by cases s <;> decide)
      (by cases s <;> rfl)) (by cases s <;> rfl) (by cases s <;> rfl)
  have g23 : MorseReach 2 ([isoU 2, isoX s 1] ++ isoCurlR true 1 ++ [isoX s 1, isoN 0])
      ([isoU 2] ++ isoCurlR true 2 ++ [isoX s 1, isoX s 1, isoN 0]) :=
    morseReach_cast_beadOps (morseReach_frame 2 2 1 1 [isoU 2] [isoX s 1, isoN 0] _ _
      (morseReach_xCurl_beadOps s) (by cases s <;> decide) (by decide))
      (by cases s <;> rfl) (by cases s <;> rfl)
  have g34 : MorseReach 2 ([isoU 2] ++ isoCurlR true 2 ++ [isoX s 1, isoX s 1, isoN 0])
      ([isoU 2] ++ isoCurlL true 3 ++ [isoX s 1, isoX s 1, isoN 0]) :=
    morseReach_cast_beadOps (morseReach_frame 0 2 2 0 [] [isoX s 1, isoX s 1, isoN 0] _ _
      morseReach_cupCurl_beadOps (by decide) (by decide)) (by cases s <;> rfl)
      (by cases s <;> rfl)
  have g45 : MorseReach 2 ([isoU 2] ++ isoCurlL true 3 ++ [isoX s 1, isoX s 1, isoN 0])
      ([isoU 2, isoX s 1, isoX s 1] ++ isoCurlL true 3 ++ [isoN 0]) :=
    morseReach_cast_beadOps (morseReach_symm (morseReach_isoBead_commR 2 1 2
      [isoX s 0, isoX s 0] [isoU 2] (isoCurlL true 3) [isoN 0] (by cases s <;> decide)
      (by cases s <;> decide) (by decide) (by decide) (by decide))) (by cases s <;> rfl)
      (by cases s <;> rfl)
  have g56 : MorseReach 2 ([isoU 2, isoX s 1, isoX s 1] ++ isoCurlL true 3 ++ [isoN 0])
      (claspSWord s ++ isoCurlL true 1) :=
    morseReach_cast_beadOps (morseReach_isoShiftComm 2 2 2 0 [isoU 2, isoX s 1, isoX s 1]
      [isoN 0] (isoCurlL true 1) [] (by decide) (by decide) (by cases s <;> rfl))
      (by cases s <;> rfl) (by cases s <;> rfl)
  exact morseReach_trans g01 (morseReach_trans g12 (morseReach_trans g23 (morseReach_trans g34
    (morseReach_trans g45 g56))))

/-- A twist above a tangle that commutes with the doubled curl. -/
private theorem mul_twist_eq_beadOps {M : Type*} [Monoid M] (K D E P₁ P₀ Q₀ Q₁ : M)
    (hD : D = E * P₁ * P₀) (hK : K * E = E * K) (h0 : P₀ * Q₀ = 1) (h1 : P₁ * Q₁ = 1) :
    K * D = D * Q₀ * Q₁ * K * P₁ * P₀ := by
  subst hD
  have h : E * P₁ * P₀ * Q₀ * Q₁ = E := by
    rw [mul_assoc (E * P₁), h0, mul_one, mul_assoc, h1, mul_one]
  rw [h, ← mul_assoc, ← mul_assoc, hK]

/-- Opposite curls on one strand cancel. -/
theorem twkOp_curl_inv (c : ℕ) :
    twkOp c (isoCurlL true 1) * twkOp c (isoCurlL false 1) = 1 ∧
      twkOp c (isoCurlL false 1) * twkOp c (isoCurlL true 1) = 1 ∧
      twkOp c (isoCurlR true 0) * twkOp c (isoCurlR false 0) = 1 ∧
      twkOp c (isoCurlR false 0) * twkOp c (isoCurlR true 0) = 1 := by
  have h3 : twkOp c (isoCurlR false 0) * twkOp c (isoCurlR true 0) = 1 :=
    twkOp_mul_eq_one_of_reach_beadOps (a := isoCurlR false 0) (b := isoCurlR true 0)
      (morseReach_cast_beadOps morseReach_isoPark_LNLP (by decide) rfl) (by decide) c
  exact ⟨twkOp_mul_eq_one_of_reach_beadOps (a := isoCurlL true 1) (b := isoCurlL false 1)
      (morseReach_cast_beadOps morseReach_isoPark_PN (by decide) rfl) (by decide) c,
    twkOp_mul_eq_one_of_reach_beadOps (a := isoCurlL false 1) (b := isoCurlL true 1)
      (morseReach_cast_beadOps morseReach_isoPark_NP (by decide) rfl) (by decide) c,
    mul_eq_one_comm.1 h3, h3⟩

/-- The full twist and the curls on the two strands commute. -/
theorem twkOp_commute (c : ℕ) :
    Commute (twkOp c (twkTw 1)) (twkOp c (isoCurlL true 1)) ∧
      Commute (twkOp c (twkTw 1)) (twkOp c (isoCurlR true 0)) ∧
      Commute (twkOp c (isoCurlR true 0)) (twkOp c (isoCurlL true 1)) := by
  exact ⟨twkOp_mul_eq_of_reach_beadOps (a := twkTw 1) (b := isoCurlL true 1)
      (a' := isoCurlL true 1) (b' := twkTw 1)
      (morseReach_cast_beadOps morseReach_isoPark_TP (by decide) (by decide)) (by decide)
      (by decide) c,
    (twkOp_mul_eq_of_reach_beadOps (a := isoCurlR true 0) (b := twkTw 1)
      (a' := twkTw 1) (b' := isoCurlR true 0)
      (morseReach_cast_beadOps morseReach_isoPark_LPT (by decide) (by decide)) (by decide)
      (by decide) c).symm,
    twkOp_mul_eq_of_reach_beadOps (a := isoCurlR true 0) (b := isoCurlL true 1)
      (a' := isoCurlL true 1) (b' := isoCurlR true 0)
      (morseReach_cast_beadOps morseReach_isoPark_LPP (by decide) (by decide)) (by decide)
      (by decide) c⟩

/-- Below the clasp a curl on the first strand is a curl on the second strand. -/
theorem twkOp_curl_clasp (σ : Bool) (c : ℕ) :
    twkOp c (isoCurlR true 0) * twkOp c (claspSWord σ) =
      twkOp c (isoCurlL true 1) * twkOp c (claspSWord σ) :=
  twkOp_mul_eq_of_reach_beadOps (morseReach_curl_clasp_beadOps σ) (by decide) (by decide) c

/-- Above the clasp a curl on the first strand is a curl on the second strand. -/
theorem twkOp_clasp_curl (σ : Bool) (c : ℕ) :
    twkOp c (claspSWord σ) * twkOp c (isoCurlR true 0) =
      twkOp c (claspSWord σ) * twkOp c (isoCurlL true 1) :=
  twkOp_mul_eq_of_reach_beadOps (morseReach_clasp_curl_beadOps σ) (by cases σ <;> decide)
    (by cases σ <;> decide) c

/-- A full twist above the clasp is a full twist below it, with two negative curls below and two
positive curls above. -/
theorem twkOp_clasp_twist (σ : Bool) (c : ℕ) :
    twkOp c (claspSWord σ) * twkOp c (twkTw 1) =
      twkOp c (twkTw 1) * twkOp c (isoCurlR false 0) * twkOp c (isoCurlL false 1) *
        twkOp c (claspSWord σ) * twkOp c (isoCurlL true 1) * twkOp c (isoCurlR true 0) := by
  have hK : morseFits 2 (claspSWord σ) = true ∧ morseOut 2 (claspSWord σ) = 2 := by
    cases σ <;> decide
  have hD : twkOp c (twkTw 1) =
      twkOp c isoDCurlL * twkOp c (isoCurlL true 1) * twkOp c (isoCurlR true 0) := by
    rw [twkOp_eq_of_morseReach (morseReach_cast_beadOps morseReach_isoPark_twistDcurl
        (by decide : twkTw 1 = isoBeadsWord [.t]) rfl) c,
      twkOp_append c _ _ (by decide) (by decide), twkOp_append c _ _ (by decide) (by decide),
      twkOp_eq_of_morseReach morseReach_curlRL_beadOps c]
  have hE : twkOp c (claspSWord σ) * twkOp c isoDCurlL =
      twkOp c isoDCurlL * twkOp c (claspSWord σ) :=
    twkOp_mul_eq_of_reach_beadOps (morseReach_cast_beadOps
      (morseReach_isoBead_dcurl 2 (claspSWord σ) [] [] hK.1 hK.2 (by decide)) (by simp)
      (by simp)) hK (by decide) c
  exact mul_twist_eq_beadOps _ _ _ _ _ _ _ hD hE (twkOp_curl_inv c).2.2.1 (twkOp_curl_inv c).1

end AJConjecture
