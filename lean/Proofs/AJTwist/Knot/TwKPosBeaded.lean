import Mathlib
import AJTwist.Knot.TwKPosWords
import AJTwist.Knot.TwKPosEvacDefs

/-!
# The junction word for `r ≥ 3` is the doubled core with beads

`isoBeaded_twkQBody` (`r ≥ 3`): `twkQBody r s σ` is `morseDouble (pairCore r s)` with
  `2 (r - 1) s + 1` beads: `(r - 1) s` blocks `A1` (the bottom block, the `z + 1` blocks of the
  increasing run, the block of the last round, the block of the top-right climb, the `q - 1`
  blocks of the right descents), `(r - 1) s` positive left curls (the `q` left climbs, the
  `E - 1` blocks of the decreasing run, round `0`, the `s - 2` rounds, the top curl) and the
  clasp. Proof: the definition of `twkQBody`, block by block (`IsoBeaded.letter`,
  `IsoBeaded.bead`, an append lemma for `IsoBeaded`), and the count
  `1 + (z + 1) + 1 + 1 + (q - 1) = c = q + (E - 1) + 1 + (s - 2) + 1` with `c = (r - 1) s`,
  `E = pairRunDown r s`, `z = pairRunUp r s`, `q = r - 2`.

Checked outside Lean (`SCR/KP/tools/evac_test.py`): the bead positions (as slots of the core) and
the counts for `(3,4), (3,5), (4,5)`; the counts for five more pairs.
-/

namespace AJConjecture

/-- Beaded words compose. -/
private theorem isoBeaded_append_twKBeaded {n : ℕ} {G W G' W' : MorseWord}
    {Bs Bs' : List MorseWord} (h : IsoBeaded n G W Bs)
    (h' : IsoBeaded (morseOut n G) G' W' Bs') :
    IsoBeaded n (G ++ G') (W ++ W') (Bs ++ Bs') := by
  induction h' with
  | nil => simpa using h
  | letter l _ ih =>
    rw [← List.append_assoc, ← List.append_assoc]
    exact IsoBeaded.letter l ih
  | bead p T _ hp hT hTo ih =>
    rw [← List.append_assoc, ← List.append_assoc]
    exact IsoBeaded.bead p T ih (by rw [morseOut_append]; exact hp) hT hTo

/-- `a` blocks `A1`, `b` positive left curls and `c` clasps. -/
private def twkBeadList (σ : Bool) (a b c : ℕ) : List MorseWord :=
  List.replicate a phaseTwoA1 ++ List.replicate b (isoCurlL true 1) ++
    List.replicate c (claspSWord σ)

/-- A piece of a beaded word: `W` is the doubled word of `G`, read from `n` thin strands and
ending on `m`, with `a` blocks `A1`, `b` positive curls and `c` clasps. -/
private def TwkBd (σ : Bool) (n m : ℕ) (G W : MorseWord) (a b c : ℕ) : Prop :=
  ∃ Bs : List MorseWord, IsoBeaded n G W Bs ∧ morseOut n G = m ∧ Bs.Perm (twkBeadList σ a b c)

/-- Pieces compose. -/
private theorem TwkBd.append {σ : Bool} {n m k : ℕ} {G W G' W' : MorseWord} {a b c a' b' c' : ℕ}
    (h : TwkBd σ n m G W a b c) (h' : TwkBd σ m k G' W' a' b' c') :
    TwkBd σ n k (G ++ G') (W ++ W') (a + a') (b + b') (c + c') := by
  obtain ⟨Bs, hB, hm, hp⟩ := h
  obtain ⟨Bs', hB', hk, hp'⟩ := h'
  subst hm
  refine ⟨Bs ++ Bs', isoBeaded_append_twKBeaded hB hB', by rw [morseOut_append, hk], ?_⟩
  refine (hp.append hp').trans (List.perm_iff_count.2 fun x ↦ ?_)
  simp only [twkBeadList, List.replicate_add, List.count_append]
  omega

/-- Changing the presentation of a piece. -/
private theorem TwkBd.of_eq {σ : Bool} {n m n' m' : ℕ} {G W G' W' : MorseWord}
    {a b c a' b' c' : ℕ} (h : TwkBd σ n m G W a b c) (hn : n = n') (hm : m = m') (hG : G = G')
    (hW : W = W') (ha : a = a') (hb : b = b') (hc : c = c') :
    TwkBd σ n' m' G' W' a' b' c' := by
  subst hn hm hG hW ha hb hc
  exact h

/-- The empty piece. -/
private theorem twkBd_nil (σ : Bool) (n : ℕ) : TwkBd σ n n [] [] 0 0 0 :=
  ⟨[], IsoBeaded.nil n, rfl, List.Perm.refl _⟩

/-- Letters of the core without beads. -/
private theorem twkBd_letters (σ : Bool) (n : ℕ) (G : MorseWord) :
    TwkBd σ n (morseOut n G) G (morseDouble G) 0 0 0 := by
  refine ⟨[], ?_, rfl, List.Perm.refl _⟩
  induction G using List.reverseRecOn with
  | nil => exact IsoBeaded.nil n
  | append_singleton G l ih =>
    have := IsoBeaded.letter l ih
    simpa only [morseDouble, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] using this

/-- Letters of the core without beads, with the number of strands at the end. -/
private theorem twkBd_letters_out (σ : Bool) (n m : ℕ) (G : MorseWord) (h : morseOut n G = m) :
    TwkBd σ n m G (morseDouble G) 0 0 0 :=
  h ▸ twkBd_letters σ n G

/-- A block `A1` on the band `p`. -/
private theorem twkBd_A1 (σ : Bool) (n p : ℕ) (hp : p < n) :
    TwkBd σ n n [] (morseShiftWord (2 * p) phaseTwoA1) 1 0 0 :=
  ⟨[] ++ [phaseTwoA1], IsoBeaded.bead p phaseTwoA1 (IsoBeaded.nil n) hp (by decide) (by decide),
    rfl, List.Perm.refl _⟩

/-- A positive left curl on the band `p`. -/
private theorem twkBd_curl (σ : Bool) (n p : ℕ) (hp : p < n) :
    TwkBd σ n n [] (morseShiftWord (2 * p) (isoCurlL true 1)) 0 1 0 :=
  ⟨[] ++ [isoCurlL true 1],
    IsoBeaded.bead p (isoCurlL true 1) (IsoBeaded.nil n) hp (by decide) (by decide),
    rfl, List.Perm.refl _⟩

/-- The clasp on the band `p`. -/
private theorem twkBd_clasp (σ : Bool) (n p : ℕ) (hp : p < n) :
    TwkBd σ n n [] (morseShiftWord (2 * p) (claspSWord σ)) 0 0 1 :=
  ⟨[] ++ [claspSWord σ], IsoBeaded.bead p (claspSWord σ) (IsoBeaded.nil n) hp
    (by cases σ <;> decide) (by cases σ <;> decide), rfl, List.Perm.refl _⟩

/-- A run of equal pieces. -/
private theorem TwkBd.blk {σ : Bool} {n : ℕ} {G W : MorseWord} {a b c : ℕ}
    (h : TwkBd σ n n G W a b c) (k : ℕ) :
    TwkBd σ n n (phaseTwoBlk G k) (phaseTwoBlk W k) (k * a) (k * b) (k * c) := by
  induction k with
  | zero => exact (twkBd_nil σ n).of_eq rfl rfl rfl rfl (by ring) (by ring) (by ring)
  | succ k ih =>
    simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons] at ih ⊢
    exact (h.append ih).of_eq rfl rfl rfl rfl (by ring) (by ring) (by ring)

/-- A run of pieces without letters. -/
private theorem TwkBd.blk_nil {σ : Bool} {n : ℕ} {W : MorseWord} {a b c : ℕ}
    (h : TwkBd σ n n [] W a b c) (k : ℕ) :
    TwkBd σ n n [] (phaseTwoBlk W k) (k * a) (k * b) (k * c) :=
  (h.blk k).of_eq rfl rfl (by simp [phaseTwoBlk]) rfl rfl rfl rfl

/-- A left walk does not change the number of strands. -/
private theorem morseOut_morseWalkL_twKBeaded (n : ℕ) (s : Bool) (p len : ℕ) :
    morseOut n (morseWalkL s p len) = n :=
  morseOut_of_cross n _ fun b hb ↦ by
    simp only [morseWalkL, List.mem_map] at hb
    obtain ⟨i, -, rfl⟩ := hb
    exact ⟨s, rfl⟩

/-- Closes equalities of explicit words with shifted positions. -/
local macro "twkb_word_eq" : tactic =>
  `(tactic| (simp only [morseShiftWord, List.map_cons, List.map_nil, List.map_append, shiftLetter,
    isoU, isoN, isoX, isoCurlL, phaseTwoA1, morseDouble, morseDoubleLetter, List.flatMap_cons,
    List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, List.cons.injEq,
    Prod.mk.injEq, true_and, and_true] <;> omega))

/-- A left climb: the cup `k` and a curl on its left band. -/
private theorem twkBd_LC (σ : Bool) (k : ℕ) :
    TwkBd σ (2 * k + 1) (2 * k + 3) [isoU k] (isoBLC (k + 1)) 0 1 0 := by
  refine ((twkBd_letters σ (2 * k + 1) [isoU k]).append
    (twkBd_curl σ (2 * k + 3) k (by omega))).of_eq rfl rfl rfl ?_ rfl rfl rfl
  rw [isoBLC, Nat.add_sub_cancel]
  twkb_word_eq

/-- The left climbs. -/
private theorem twkBd_LCs (σ : Bool) (m : ℕ) :
    TwkBd σ 1 (2 * m + 1) ((List.range m).map isoU)
      ((List.range m).flatMap fun i ↦ isoBLC (i + 1)) 0 m 0 := by
  induction m with
  | zero => exact twkBd_nil σ 1
  | succ m ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_append, List.map_cons, List.map_nil]
    exact (ih.append (twkBd_LC σ m)).of_eq rfl (by ring) rfl rfl rfl rfl rfl

/-- A right descent: a block `A1` and the cap `k`. -/
private theorem twkBd_Rd (σ : Bool) (k : ℕ) :
    TwkBd σ (2 * k + 3) (2 * k + 1) [isoN k] (isoBRd (k + 1)) 1 0 0 := by
  refine ((twkBd_A1 σ (2 * k + 3) k (by omega)).append
    (twkBd_letters σ (2 * k + 3) [isoN k])).of_eq rfl rfl rfl ?_ rfl rfl rfl
  rw [isoBRd, Nat.add_sub_cancel]

/-- The right descents. -/
private theorem twkBd_Rds (σ : Bool) (m : ℕ) :
    TwkBd σ (2 * m + 1) 1 ((List.range m).reverse.map isoN)
      ((List.range m).reverse.flatMap fun i ↦ isoBRd (i + 1)) m 0 0 := by
  induction m with
  | zero => exact twkBd_nil σ 1
  | succ m ih =>
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.flatMap_cons, List.map_cons]
    exact ((twkBd_Rd σ m).append ih).of_eq (by ring) rfl rfl rfl (by ring) rfl rfl

/-- A run of `k + 2` blocks: the first block, `k` blocks, the last block. -/
private theorem phaseTwoBlk_add_two_twKBeaded (w : MorseWord) (k : ℕ) :
    phaseTwoBlk w (k + 2) = w ++ phaseTwoBlk w k ++ w := by
  simp only [phaseTwoBlk, List.replicate_succ, List.flatten_cons, List.append_assoc]
  congr 1
  rw [← List.flatten_cons, ← List.replicate_succ, List.replicate_succ', List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil]

/-- The junction word as a piece: the doubled core with its beads, counted. -/
private theorem twkBd_twkQBody (σ : Bool) (t k : ℕ) :
    TwkBd σ 1 1 (pairCore (t + 3) (k + 2)) (twkQBody (t + 3) (k + 2) σ)
      (pairRunUp (t + 3) (k + 2) + t + 4) (t + pairRunDown (t + 3) (k + 2) + k + 2) 1 := by
  have pBot : TwkBd σ 1 1 [] phaseTwoA1 1 0 0 :=
    (twkBd_A1 σ 1 0 (by omega)).of_eq rfl rfl rfl (morseShiftWord_zero_iso _) rfl rfl rfl
  have pTop : TwkBd σ 1 1 [] (isoCurlL true 1) 0 1 0 :=
    (twkBd_curl σ 1 0 (by omega)).of_eq rfl rfl rfl (morseShiftWord_zero_iso _) rfl rfl rfl
  have pDec : TwkBd σ (2 * t + 3) (2 * t + 3) [] (isoBDec (t + 1)) 0 1 0 :=
    (twkBd_curl σ _ t (by omega)).of_eq rfl rfl rfl (by rw [isoBDec, Nat.add_sub_cancel]) rfl
      rfl rfl
  have pInc : TwkBd σ (2 * t + 3) (2 * t + 3) [] (isoBInc (t + 1)) 1 0 0 :=
    twkBd_A1 σ _ (t + 1) (by omega)
  have hW : ∀ n, morseOut n (morseWalkL true (t + 1) (t + 2)) = n := fun n ↦
    morseOut_morseWalkL_twKBeaded n true _ _
  have pR0 : TwkBd σ (2 * t + 3) (2 * t + 5) ([isoU (2 * t + 3)] ++ morseWalkL true (t + 1) (t + 2))
      (isoBR0 (t + 1) (t + 3)) 0 1 0 :=
    ((twkBd_letters_out σ (2 * t + 3) (2 * t + 5)
      ([isoU (2 * t + 3)] ++ morseWalkL true (t + 1) (t + 2))
      (by rw [morseOut_append, hW]; rfl)).append
      (twkBd_curl σ (2 * t + 5) (t + 1) (by omega))).of_eq rfl rfl (List.append_nil _)
      (by rw [isoBR0, show t + 1 + (t + 3) - 1 = 2 * t + 3 by omega,
        show t + 3 - 1 = t + 2 by omega]) rfl rfl rfl
  have pClasp : TwkBd σ (2 * t + 5) (2 * t + 5) []
      (morseShiftWord (2 * (t + 1) + 2 * (t + 3)) (claspSWord σ)) 0 0 1 :=
    (twkBd_clasp σ _ (2 * t + 4) (by omega)).of_eq rfl rfl rfl
      (by rw [show 2 * (t + 1) + 2 * (t + 3) = 2 * (2 * t + 4) by ring]) rfl rfl rfl
  have pRound : TwkBd σ (2 * t + 5) (2 * t + 5) (morseWalkL true (t + 1) (t + 2))
      (isoBRound (t + 1) (t + 3)) 0 1 0 :=
    ((twkBd_letters_out σ (2 * t + 5) (2 * t + 5) (morseWalkL true (t + 1) (t + 2))
      (hW _)).append (twkBd_curl σ (2 * t + 5) (t + 1) (by omega))).of_eq
      rfl rfl (List.append_nil _) (by rw [isoBRound, show t + 3 - 1 = t + 2 by omega]) rfl rfl rfl
  have pLast : TwkBd σ (2 * t + 5) (2 * t + 3) (morseWalkL true (t + 1) (t + 2) ++ [isoN t])
      (isoBLast (t + 1) (t + 3)) 1 0 0 :=
    ((twkBd_A1 σ (2 * t + 5) t (by omega)).append
      (twkBd_letters_out σ (2 * t + 5) (2 * t + 3) (morseWalkL true (t + 1) (t + 2) ++ [isoN t])
        (by rw [morseOut_append, hW]; rfl))).of_eq rfl rfl rfl
      (by rw [isoBLast, show t + 3 - 1 = t + 2 by omega, Nat.add_sub_cancel]) rfl rfl rfl
  have pTrcA : TwkBd σ (2 * t + 3) (2 * t + 3) []
      (morseShiftWord (4 * (t + 1) - 2) phaseTwoA1) 1 0 0 :=
    (twkBd_A1 σ _ (2 * t + 1) (by omega)).of_eq rfl rfl rfl
      (by rw [show 4 * (t + 1) - 2 = 2 * (2 * t + 1) by omega]) rfl rfl rfl
  have pCap : TwkBd σ (2 * t + 3) (2 * t + 1) [isoN (2 * t + 1)]
      (morseDouble [isoN (2 * (t + 3) - 5)]) 0 0 0 :=
    (twkBd_letters_out σ (2 * t + 3) (2 * t + 1) [isoN (2 * t + 1)] rfl).of_eq rfl rfl rfl
      (by rw [show 2 * (t + 3) - 5 = 2 * t + 1 by omega]) rfl rfl rfl
  have hall := pBot.append ((twkBd_LCs σ t).append ((twkBd_LC σ t).append
    ((pDec.blk_nil (pairRunDown (t + 3) (k + 2) - 1)).append
    ((pInc.blk_nil (pairRunUp (t + 3) (k + 2) + 1)).append (pR0.append (pClasp.append
    ((pRound.blk k).append (pLast.append (pTrcA.append (pCap.append
    ((twkBd_Rds σ t).append pTop)))))))))))
  refine hall.of_eq rfl rfl ?_ ?_ ?_ ?_ ?_
  · simp only [pairCore, show t + 3 - 2 = t + 1 by omega, show t + 3 - 3 = t by omega,
      show t + 3 - 1 = t + 2 by omega, show 2 * (t + 3) - 3 = 2 * t + 3 by omega,
      show 2 * (t + 3) - 5 = 2 * t + 1 by omega, phaseTwoBlk_add_two_twKBeaded, List.range_succ,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.nil_append,
      List.cons_append, List.append_nil]
  · simp only [twkQBody, show t + 3 - 2 = t + 1 by omega, Nat.add_sub_cancel, Nat.add_sub_cancel,
      List.append_assoc]
  · omega
  · have : 1 ≤ pairRunDown (t + 3) (k + 2) := by simp [pairRunDown]
    omega
  · omega

/-- `twkQBody r s σ` is the doubled core with `(r-1)s` blocks `A1`, `(r-1)s` positive curls and
the clasp. -/
theorem isoBeaded_twkQBody {r s : ℕ} (h : IsTorusPair r s) (hr : 3 ≤ r) (σ : Bool) :
    ∃ Bs : List MorseWord, IsoBeaded 1 (pairCore r s) (twkQBody r s σ) Bs ∧
      Bs.Perm (List.replicate ((r - 1) * s) phaseTwoA1 ++
        List.replicate ((r - 1) * s) (isoCurlL true 1) ++ [claspSWord σ]) := by
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 3 := ⟨r - 3, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by have := h.2.1; omega⟩
  obtain ⟨Bs, hB, -, hp⟩ := twkBd_twkQBody σ t k
  refine ⟨Bs, hB, ?_⟩
  have h1 : (t + 2) * (k + 2) = t * k + 2 * t + 2 * k + 4 := by ring
  have h2 : (t + 1) * (k + 1) = t * k + t + k + 1 := by ring
  have ha : pairRunUp (t + 3) (k + 2) + t + 4 = (t + 3 - 1) * (k + 2) := by
    simp only [pairRunUp, pairC, show t + 3 - 1 = t + 2 by omega]
    omega
  have hb : t + pairRunDown (t + 3) (k + 2) + k + 2 = (t + 3 - 1) * (k + 2) := by
    simp only [pairRunDown, show t + 3 - 1 = t + 2 by omega, show t + 3 - 2 = t + 1 by omega,
      show k + 2 - 1 = k + 1 by omega]
    omega
  rw [ha, hb] at hp
  exact hp

end AJConjecture
