import Mathlib
import AJConjecture.ClaspAlgScalars
import AJConjecture.SkeinHalfTwist
import AJConjecture.SkeinPlace

/-!
# The algebra of two bundles

Two adjacent bundles of `c` strands, each carrying the Jones–Wenzl projector `f_c`, in
`V^{⊗ 2c}`. The turnback element `D_k = (f ⊗ f) E^{(k)} (f ⊗ f)` has `k` nested caps followed by
`k` nested cups on the `2k` middle strands (`D_0 = f ⊗ f`, `D_1 = (f ⊗ f) e_{c-1} (f ⊗ f)`, and
`D_k = 0` for `k > c`, when the nested caps do not fit). The element `D_1` is diagonalisable on
the image of `f ⊗ f` with the `c + 1` distinct eigenvalues `d_{1,n}` of
`AJConjecture.claspAlgTurnbackEigen`, and `channelIdem c n` is its spectral idempotent `Q_n`
(Lagrange interpolation): the projection on the channel of colour `2n`. The fusion maps
`π = (f ⊗ f) · caps · f_{2n}` and `ι = f_{2n} · cups · (f ⊗ f)` between two bundles of `n + m`
strands and one bundle of `2n` strands close the `2m` middle strands by `m` nested caps or cups.
Sizes are written so that no subtraction occurs in a type.
-/

noncomputable section

namespace AJConjecture

/-- The turnback element `D_k = (f ⊗ f) E^{(k)} (f ⊗ f)` of two bundles of `c` strands. -/
def turnback (c k : ℕ) : SkMat (2 * c) (2 * c) :=
  twoBundleProj c * skPlace (2 * c) (2 * c) (c - k) (capThick k * cupThick k) * twoBundleProj c

/-- The spectral idempotent `Q_n` of `D_1` for the eigenvalue `d_{1,n}`: the channel of colour
`2n` in the product of two bundles of `c` strands. -/
def channelIdem (c n : ℕ) : SkMat (2 * c) (2 * c) :=
  twoBundleProj c * (((List.range (c + 1)).filter (· ≠ n)).map fun m ↦
    (claspAlgTurnbackEigen c 1 n - claspAlgTurnbackEigen c 1 m)⁻¹ •
      (turnback c 1 - claspAlgTurnbackEigen c 1 m • (1 : SkMat (2 * c) (2 * c)))).prod

/-- The fusion map `π` from two bundles of `n + m` strands to one bundle of `2n` strands:
`f ⊗ f`, then `m` nested caps on the `2m` middle strands, then `f_{2n}`. -/
def fusionProj (n m : ℕ) : SkMat (2 * (n + m)) (2 * n) :=
  twoBundleProj (n + m) * skPlace (2 * (n + m)) (2 * n) n (capThick m) * jwAt (2 * n) 0 (2 * n)

/-- The fusion map `ι` from one bundle of `2n` strands to two bundles of `n + m` strands:
`f_{2n}`, then `m` nested cups in the middle, then `f ⊗ f`. -/
def fusionIncl (n m : ℕ) : SkMat (2 * n) (2 * (n + m)) :=
  jwAt (2 * n) 0 (2 * n) * skPlace (2 * n) (2 * (n + m)) n (cupThick m) * twoBundleProj (n + m)

end AJConjecture
