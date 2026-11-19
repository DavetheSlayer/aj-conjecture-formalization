import Mathlib
import AJConjecture.SkeinBandRotProj
import AJConjecture.SkeinTwoBundle

/-!
# The rotation exchanges the turnback elements `D_k` and `D_{c-k}`

Without projectors: the rotation of `k` nested cap–cups on the `2k` middle strands (the other
`c - k` strands of each bundle going straight) is `c - k` nested cap–cups on the `2(c - k)` middle
strands. Split the nests of `c` cups and `c` caps of the rotation into their `k` outer and `c - k`
inner strands (`AJConjecture.cupThick_add`, `AJConjecture.capThick_add`): the straight strands of
the operator join the inner caps to the inner cups of the rotation and give the new nest of
cap–cups, and its cap–cups are straightened with the outer cups and caps of the rotation by the
thick zig-zag identities (`AJConjecture.cupThick_mul_capThick_left`,
`AJConjecture.cupThick_mul_capThick_right`). With projectors, by
`AJConjecture.twoBundleProj_mul_bandRot_mul_twoBundleProj` and
`AJConjecture.twoBundleProj_mul_self`:
`rot(D_k) = D_{c-k}`.
-/

namespace AJConjecture

/-- The thick zig-zag with the cups on the right, placed on a window of `n` strands. -/
private theorem skPlace_cupThick_mul_capThick_bandRotTurnback (n N i j k : ℕ) (hi : i + k ≤ n)
    (hN : N = n + 2 * k) (hj : j = i + k) :
    skPlace n N j (cupThick k) * skPlace N n i (capThick k) = 1 := by
  subst hN hj
  have h := congrArg (skPlace n n i) (cupThick_mul_capThick_right k)
  rw [skPlace_mul n (n + 2 * k) n i _ _ hi (by omega) (by omega),
    skPlace_skPlace n (n + 2 * k) i k (cupThick k) (by omega) (by omega) (by omega) (by omega),
    skPlace_skPlace (n + 2 * k) n i 0 (capThick k) (by omega) (by omega) (by omega) (by omega),
    skPlace_one n i k hi, Nat.add_zero] at h
  exact h

/-- The chain of rewritings for the rotation of a nest of cap–cups. -/
private theorem zigzag_chain_bandRotTurnback {a b c d : ℕ} (Uk : SkMat a b) (Ur : SkMat b c)
    (Mcap : SkMat c d) (Mcup : SkMat d c) (Wr : SkMat c b) (Wk : SkMat b a) (Ck : SkMat b a)
    (Cr : SkMat a d) (Dr : SkMat d a) (Dk : SkMat a b) (hA : Ur * Mcap = Ck * Cr)
    (hB : Uk * Ck = 1) (hC : Mcup * Wr = Dr * Dk) (hD : Dk * Wk = 1) :
    Uk * Ur * (Mcap * Mcup) * (Wr * Wk) = Cr * Dr := by
  calc Uk * Ur * (Mcap * Mcup) * (Wr * Wk) = Uk * (Ur * Mcap) * (Mcup * Wr) * Wk := by
        simp only [Matrix.mul_assoc]
    _ = Uk * Ck * Cr * Dr * (Dk * Wk) := by rw [hA, hC]; simp only [Matrix.mul_assoc]
    _ = Cr * Dr := by rw [hB, hD, Matrix.one_mul, Matrix.mul_one]

/-- The cups of the rotation: the `k` outer cups, then the `r` inner cups. -/
private theorem skPlace_cupThick_add_bandRotTurnback (k r : ℕ) :
    skPlace (2 * (k + r)) (4 * (k + r)) (2 * (k + r)) (cupThick (k + r)) =
      skPlace (2 * (k + r)) (2 * (k + r) + 2 * k) (2 * (k + r)) (cupThick k) *
        skPlace (2 * (k + r) + 2 * k) (4 * (k + r)) (2 * (k + r) + k) (cupThick r) := by
  rw [cupThick_add k r,
    skPlace_mul (2 * (k + r)) (2 * (k + r) + 2 * k) (4 * (k + r)) (2 * (k + r)) _ _ (by omega)
      (by omega) (by omega),
    skPlace_skPlace _ _ (2 * (k + r)) k (cupThick r) (by omega) (by omega) (by omega) (by omega)]

/-- The caps of the rotation: the `r` inner caps, then the `k` outer caps. -/
private theorem skPlace_capThick_add_bandRotTurnback (k r : ℕ) :
    skPlace (4 * (k + r)) (2 * (k + r)) 0 (capThick (k + r)) =
      skPlace (4 * (k + r)) (2 * (k + r) + 2 * k) k (capThick r) *
        skPlace (2 * (k + r) + 2 * k) (2 * (k + r)) 0 (capThick k) := by
  rw [capThick_add k r,
    skPlace_mul (4 * (k + r)) (2 * (k + r) + 2 * k) (2 * (k + r)) 0 _ _ (by omega) (by omega)
      (by omega),
    skPlace_skPlace _ _ 0 k (capThick r) (by omega) (by omega) (by omega) (by omega),
    Nat.zero_add]

/-- The nest of cap–cups placed in the middle of four bundles. -/
private theorem skPlace_nest_bandRotTurnback (k r : ℕ) :
    skPlace (4 * (k + r)) (4 * (k + r)) (k + r)
        (skPlace (2 * (k + r)) (2 * (k + r)) r (capThick k * cupThick k)) =
      skPlace (4 * (k + r)) (2 * (k + r) + 2 * r) (k + r + r) (capThick k) *
        skPlace (2 * (k + r) + 2 * r) (4 * (k + r)) (k + r + r) (cupThick k) := by
  rw [skPlace_skPlace _ _ (k + r) r _ (by omega) (by omega) (by omega) (by omega),
    skPlace_mul (4 * (k + r)) (2 * (k + r) + 2 * r) (4 * (k + r)) (k + r + r) _ _ (by omega)
      (by omega) (by omega)]

/-- The rotation of `k` nested cap–cups in two bundles of `k + r` strands. -/
private theorem bandRot_nest_bandRotTurnback (k r : ℕ) :
    bandRot (k + r) (skPlace (2 * (k + r)) (2 * (k + r)) r (capThick k * cupThick k)) =
      skPlace (2 * (k + r)) (2 * (k + r)) k (capThick r * cupThick r) := by
  have hA := skPlace_mul_skPlace_comm (2 * (k + r) + 2 * k) (2 * (k + r)) (4 * (k + r))
    (2 * (k + r) + 2 * r) (k + r + r) (2 * (k + r) + k) (capThick k) (cupThick r) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  rw [show 2 * (k + r) + k + 0 - 2 * k = k + r + r from by omega] at hA
  have hB := skPlace_cupThick_mul_capThick_bandRotTurnback (2 * (k + r)) (2 * (k + r) + 2 * k)
    (k + r + r) (2 * (k + r)) k (by omega) rfl (by omega)
  have hC := skPlace_mul_skPlace_comm (2 * (k + r) + 2 * r) (2 * (k + r)) (4 * (k + r))
    (2 * (k + r) + 2 * k) k (k + r + r) (capThick r) (cupThick k) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  rw [show k + r + r + 0 - 2 * r = k from by omega] at hC
  have hD := skPlace_cupThick_mul_capThick_bandRotTurnback (2 * (k + r)) (2 * (k + r) + 2 * k)
    0 k k (by omega) rfl (by omega)
  have hE := skPlace_mul_skPlace_comm (2 * (k + r)) (2 * k) (2 * (k + r) + 2 * r)
    (2 * (k + r)) k (k + r + r) (capThick r) (cupThick r) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  rw [show k + r + r + 0 - 2 * r = k from by omega] at hE
  rw [bandRot, skPlace_cupThick_add_bandRotTurnback, skPlace_capThick_add_bandRotTurnback,
    skPlace_nest_bandRotTurnback,
    zigzag_chain_bandRotTurnback _ _ _ _ _ _ _ _ _ _ hA.symm hB hC.symm hD, ← hE,
    skPlace_mul (2 * (k + r)) (2 * k) (2 * (k + r)) k _ _ (by omega) (by omega) (by omega)]

/-- The rotation of `k` nested cap–cups is `c - k` nested cap–cups. -/
theorem bandRot_capThick_mul_cupThick (c k : ℕ) (hk : k ≤ c) :
    bandRot c (skPlace (2 * c) (2 * c) (c - k) (capThick k * cupThick k)) =
      skPlace (2 * c) (2 * c) k (capThick (c - k) * cupThick (c - k)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left]
  exact bandRot_nest_bandRotTurnback k r

/-- The rotation exchanges `D_k` and `D_{c-k}`. -/
theorem bandRot_turnback (c k : ℕ) (hk : k ≤ c) :
    bandRot c (turnback c k) = turnback c (c - k) := by
  rw [turnback, turnback, ← twoBundleProj_mul_bandRot_mul_twoBundleProj,
    bandRot_capThick_mul_cupThick c k hk, Nat.sub_sub_self hk]

end AJConjecture
