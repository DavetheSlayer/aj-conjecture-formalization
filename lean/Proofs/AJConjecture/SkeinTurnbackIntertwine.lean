import Mathlib
import AJConjecture.SkeinTurnbackEigenBasic
import AJConjecture.SkeinTurnbackOneSided

/-!
# A nest of caps intertwines the turnback elements of two bundle sizes

With `Γ = (f ⊗ f) · caps_k` from two bundles of `c = a + 1 + k` strands to two bundles of `a + 1`
strands: `D_1 Γ = Γ (β_k + α_k D'_1)`, where `D'_1` is the turnback element of the smaller bundles,
`β_k = -[k][2c+1-k]/[c]²`, `α_k = [a+1]²/[c]²`. This is the one-sided recursion
`AJConjecture.turnback_one_mul_capThick_place` rewritten: the nest of `k + 1` caps is the nest of
`k` caps followed by the outer cap (`AJConjecture.capThick_succ`), the outer cap followed by the
cup is the generator `e_a` of the smaller bundles (`AJConjecture.capAt_mul_cupAt`), and the
projectors of the smaller bundles are absorbed
(`AJConjecture.twoBundleProj_mul_capThick_mul_twoBundleProj`). On the eigenvalues:
`β_k + α_k d'_{1,n'} = d_{1,n'}`, that is `[k][2n+k+1] + [n-n'][n+n'+1] = [n+k-n'][n+k+n'+1]`, an
identity
of Laurent polynomials in `t`; so `Γ` sends the channel `n'` of the smaller bundles to the channel
`n'` of the larger ones.
-/

namespace AJConjecture

/-- The nest of `k` caps followed by the generator `e_a` of the smaller bundles is the nest of
`k + 1` caps followed by a cup. -/
private theorem capThick_place_mul_tlGenF_intertwine (a k : ℕ) :
    skPlace (2 * (a + 1 + k)) (2 * a + 2) (a + 1) (capThick k) * tlGenF (2 * a + 2) a =
      skPlace (2 * (a + 1 + k)) (2 * a) a (capThick (k + 1)) * cupAt (2 * a) a := by
  rw [capThick_succ,
    skPlace_mul (2 * (a + 1 + k)) (2 * a + 2) (2 * a) a _ skCap (by omega) (by omega) (by omega),
    skPlace_skPlace (2 * (a + 1 + k)) (2 * a + 2) a 1 (capThick k) (by omega) (by omega)
      (by omega) (by omega),
    Matrix.mul_assoc, ← capAt_mul_cupAt (2 * a) a (by omega)]
  rfl

/-- The nest of caps intertwines `D_1` with `β_k + α_k D'_1`. -/
theorem turnback_one_mul_twoBundleProj_capThick (a k : ℕ) :
    turnback (a + 1 + k) 1 *
        (twoBundleProj (a + 1 + k) *
          skPlace (2 * (a + 1 + k)) (2 * (a + 1)) (a + 1) (capThick k)) =
      twoBundleProj (a + 1 + k) * skPlace (2 * (a + 1 + k)) (2 * (a + 1)) (a + 1) (capThick k) *
        ((-(quantumInt (k : ℤ) * quantumInt (2 * (a : ℤ) + k + 3)) /
            quantumInt ((a : ℤ) + 1 + k) ^ 2) • twoBundleProj (a + 1) +
          (quantumInt ((a : ℤ) + 1) ^ 2 / quantumInt ((a : ℤ) + 1 + k) ^ 2) •
            turnback (a + 1) 1) := by
  have hkey : skPlace (2 * (a + 1 + k)) (2 * (a + 1)) (a + 1) (capThick k) *
      tlGenF (2 * (a + 1)) a =
        skPlace (2 * (a + 1 + k)) (2 * a) a (capThick (k + 1)) *
          skPlace (2 * a) (2 * (a + 1)) a skCup :=
    capThick_place_mul_tlGenF_intertwine a k
  rw [← Matrix.mul_assoc, turnback_mul_twoBundleProj, turnback_one_mul_capThick_place,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    twoBundleProj_mul_capThick_mul_twoBundleProj (a + 1) k, turnback_one (a + 1),
    Nat.add_sub_cancel, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    twoBundleProj_mul_capThick_mul_twoBundleProj (a + 1) k,
    Matrix.mul_assoc (twoBundleProj (a + 1 + k)) _ (tlGenF (2 * (a + 1)) a), hkey,
    ← Matrix.mul_assoc]

/-- The eigenvalues of `D_1` for two bundle sizes: `β_k + α_k d'_{1,n'} = d_{1,n'}`. -/
theorem turnbackEigen_one_add (n k n' : ℕ) (h : n' ≤ n) :
    -(quantumInt (k : ℤ) * quantumInt (2 * (n : ℤ) + k + 1)) / quantumInt ((n : ℤ) + k) ^ 2 +
        quantumInt (n : ℤ) ^ 2 / quantumInt ((n : ℤ) + k) ^ 2 * claspAlgTurnbackEigen n 1 n' =
      claspAlgTurnbackEigen (n + k) 1 n' := by
  unfold claspAlgTurnbackEigen
  rw [Finset.prod_range_one, Finset.prod_range_one]
  simp only [Nat.cast_zero, sub_zero, Nat.cast_add]
  have key := quantumInt_mul_shift_sub ((n : ℤ) - n') ((n : ℤ) + n' + 1) k
  rw [show (n : ℤ) - n' + k = (n : ℤ) + k - n' from by ring,
    show (n : ℤ) + n' + 1 + k = (n : ℤ) + k + n' + 1 from by ring,
    show (n : ℤ) - n' + ((n : ℤ) + n' + 1) + k = 2 * (n : ℤ) + k + 1 from by ring] at key
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : n' = 0 := by omega
    have h0 : quantumInt 0 = 0 := by simp [quantumInt]
    simp [h0]
  · have hn0 : quantumInt (n : ℤ) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    have hnk : quantumInt ((n : ℤ) + k) ≠ 0 := claspAlg_quantumInt_ne_zero (by omega)
    field_simp
    linear_combination key

end AJConjecture
