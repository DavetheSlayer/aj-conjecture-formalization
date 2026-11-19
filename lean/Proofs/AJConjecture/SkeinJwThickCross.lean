import Mathlib
import AJConjecture.SkeinJwCapComm
import AJConjecture.SkeinJonesWenzl
import AJConjecture.SkeinThickCrossTl

/-!
# The Jones–Wenzl projector slides through a thick crossing

`f` on a bundle is built from the generators of that bundle by Wenzl's recursion, and each
generator slides through the crossing; induction on the size of the projector.
-/

namespace AJConjecture

/-- The projector on the first bundle slides through a thick crossing. -/
theorem jwAt_mul_braidMatrix_thickCross_fst (n a b off : ℕ) (s : Bool) (hn : off + a + b ≤ n) :
    jwAt n off a * braidMatrix n (thickCross a b off s) =
      braidMatrix n (thickCross a b off s) * jwAt n (off + b) a :=
  jwAt_mul_eq_mul_jwAt n n off (off + b) _ a fun l hl ↦
    tlGenF_mul_braidMatrix_thickCross_fst n a b off l s hn (by omega)

/-- The projector on the second bundle slides through a thick crossing. -/
theorem jwAt_mul_braidMatrix_thickCross_snd (n a b off : ℕ) (s : Bool) (hn : off + a + b ≤ n) :
    jwAt n (off + a) b * braidMatrix n (thickCross a b off s) =
      braidMatrix n (thickCross a b off s) * jwAt n off b :=
  jwAt_mul_eq_mul_jwAt n n (off + a) off _ b fun l hl ↦
    tlGenF_mul_braidMatrix_thickCross_snd n a b off l s hn (by omega)

end AJConjecture
