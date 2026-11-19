import Mathlib
import AJConjecture.SkeinMat
import AJConjecture.SkeinJonesWenzl
import AJConjecture.SkeinPlace
import AJConjecture.SkeinThickCable
import AJConjecture.SkeinPartialTrace
import AJConjecture.SkeinScalars
import AJConjecture.SkeinHalfTwist
import AJConjecture.ColoredJones

/-!
# The torus input: definitions of the route

Definitions for the proof of `pairQ_torusInput` (the coloured Jones polynomial of `T(r, s)` at
the odd colours). The route (design notes, stages RA1–RA6):

* **RA1** two bundles of unequal thickness `a`, `b` with projectors `f_a ⊗ f_b`
  (`rjBundleProj`): the fusion maps `rjFusionProj a b j` (close `j` middle strands by nested caps,
  then `f_(a+b-2j)`) and `rjFusionIncl a b j`, their bubble scalar `rjFusionDim`, the full twist
  `rjFullTwist a b` of the two bundles and its eigenvalue `rjTwistRatio a b j`;
* **RA2** the cabled cyclic braid `c = σ_0 ⋯ σ_(r-2)` on `r` bundles of `b` strands
  (`rjCycleMat`), the column projectors `f_b^{⊗ r}` (`rjColsProj`), the spectrum `rjSpec` and the
  eigenvalues `rjTwistEigen` of `c^r`, and the spectral idempotents `rjIsoProj` (Lagrange
  polynomials in `c^r`); `RJGoodFamily` is the inductive invariant (a complete family of fusion
  maps through single projectors) from which the spectral decomposition is read off;
* **RA5** the axis loop `rjAxisLoop m k` (a bundle of `k` strands with `f_k` encircling `m`
  strands), its Hopf scalar `rjHopf`, the trace of `c` on an isotypic part `rjCycleValue`, and the
  coloured-closure calculus (`rjProfileProj`, `rjColorTrace`, `RJBraidEq`, the words
  `rjAxisWord`, `rjBetaWord`) for the isotopy `closure(c) ∪ axis ≅ T(2, 2r)`;
* **RA4** the field embedding `rjEmbed r : t ↦ t^r` of `ℚ(t)` and the `r`-th roots `rjNu`.

`RJNat` is the naturality used throughout: a map between bundles slides through the full twist
with any bundle on its right.
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-! ### RA1: two bundles of unequal thickness -/

/-- The projector `f_a ⊗ f_b` on two adjacent bundles of `a` and `b` strands. -/
def rjBundleProj (a b : ℕ) : SkMat (a + b) (a + b) :=
  jwAt (a + b) 0 a * jwAt (a + b) a b

/-- The full twist `Δ²` of a bundle of `a` strands with the bundle of `b` strands on its right:
the first bundle crosses over the second, then the second crosses back. -/
def rjFullTwist (a b : ℕ) : SkMat (a + b) (a + b) :=
  braidMatrix (a + b) (thickCross a b 0 true ++ thickCross b a 0 true)

/-- The first turnback `D_1 = (f_a ⊗ f_b) e_(a-1) (f_a ⊗ f_b)`: the last strand of the first bundle
turns back into the first strand of the second. -/
def rjTurnbackOne (a b : ℕ) : SkMat (a + b) (a + b) :=
  rjBundleProj a b * tlGenF (a + b) (a - 1) * rjBundleProj a b

/-- The fusion map of the channel `j` (`j ≤ min a b`): `f_a ⊗ f_b`, then `j` nested caps joining
the last `j` strands of the first bundle to the first `j` strands of the second, then
`f_(a+b-2j)`. -/
def rjFusionProj (a b j : ℕ) : SkMat (a + b) (a + b - 2 * j) :=
  rjBundleProj a b * skPlace (a + b) (a + b - 2 * j) (a - j) (capThick j) *
    jwAt (a + b - 2 * j) 0 (a + b - 2 * j)

/-- The fusion inclusion of the channel `j`: `f_(a+b-2j)`, then `j` nested cups, then
`f_a ⊗ f_b`. -/
def rjFusionIncl (a b j : ℕ) : SkMat (a + b - 2 * j) (a + b) :=
  jwAt (a + b - 2 * j) 0 (a + b - 2 * j) * skPlace (a + b - 2 * j) (a + b) (a - j) (cupThick j) *
    rjBundleProj a b

/-- The bubble scalar `d_j` of the channel `j`:
`∏_{i<j} -[i+1][a+b-2j+i+2] / ([a-j+i+1][b-j+i+1])`, so that `ι_j π_j = d_j f_(a+b-2j)`. -/
def rjFusionDim (a b j : ℕ) : RatFunc ℚ :=
  ∏ i ∈ Finset.range j,
    -(quantumInt ((i : ℤ) + 1) * quantumInt ((a : ℤ) + b - 2 * j + i + 2)) /
      (quantumInt ((a : ℤ) - j + i + 1) * quantumInt ((b : ℤ) - j + i + 1))

/-- The eigenvalue `θ_(a+b-2j) / (θ_a θ_b)` of the full twist on the channel `j`. -/
def rjTwistRatio (a b j : ℕ) : RatFunc ℚ :=
  kinkScalar (a + b - 2 * j) / (kinkScalar a * kinkScalar b)

/-- The eigenvalue `ν_j = -[j][a+b+1-j] / ([a][b])` of the first turnback on the channel `j`. -/
def rjTurnbackEigen (a b j : ℕ) : RatFunc ℚ :=
  -(quantumInt (j : ℤ) * quantumInt ((a : ℤ) + b + 1 - j)) /
    (quantumInt (a : ℤ) * quantumInt (b : ℤ))

/-- The first coefficient `χ = -[a+b+2] / ([a+1][b+1])` of the bubble lemma. -/
def rjBubbleChi (a b : ℕ) : RatFunc ℚ :=
  -quantumInt ((a : ℤ) + b + 2) / (quantumInt ((a : ℤ) + 1) * quantumInt ((b : ℤ) + 1))

/-- The second coefficient `ψ = [a][b] / ([a+1][b+1])` of the bubble lemma. -/
def rjBubblePsi (a b : ℕ) : RatFunc ℚ :=
  quantumInt (a : ℤ) * quantumInt (b : ℤ) / (quantumInt ((a : ℤ) + 1) * quantumInt ((b : ℤ) + 1))

/-! ### Naturality -/

/-- A map `X` from a bundle of `m` strands to a bundle of `n` strands is *natural* if it
intertwines the weights of the quantum trace and slides through the full twist with a bundle of
any thickness `k` on its right. Projectors, caps and cups inside a bundle, and their products and
transposes, are natural. -/
def RJNat {m n : ℕ} (X : SkMat m n) : Prop :=
  skWeight m * X = X * skWeight n ∧
    ∀ k : ℕ, rjFullTwist m k * skPlace (m + k) (n + k) 0 X =
      skPlace (m + k) (n + k) 0 X * rjFullTwist n k

/-! ### RA2: the cyclic braid on `r` bundles and its spectral idempotents -/

/-- The braid word `σ_0 σ_1 ⋯ σ_(r-2)` on `r` strands (`torusPairWord r s` is its `s`-th
power). -/
def rjCycleWord (r : ℕ) : BraidWord :=
  (List.range (r - 1)).map fun i ↦ (i, true)

/-- The `b`-cable of the cyclic braid `σ_0 ⋯ σ_(r-2)`, on `b r` strands. -/
def rjCycleMat (b r : ℕ) : SkMat (b * r) (b * r) :=
  braidMatrix (b * r) (cable b (rjCycleWord r))

/-- The column projectors `f_b^{⊗ r}` on `r` bundles of `b` strands. -/
def rjColsProj (b r : ℕ) : SkMat (b * r) (b * r) :=
  ((List.range r).map fun i ↦ jwAt (b * r) (b * i) b).prod

/-- The spectrum: the colours `N ≤ b r` with `N ≡ b r (mod 2)`. -/
def rjSpec (b r : ℕ) : Finset ℕ :=
  (Finset.range (b * r / 2 + 1)).image fun j ↦ b * r - 2 * j

/-- The eigenvalue `μ_N = θ_N / θ_b^r` of the cabled full twist `c^r` on the colour `N`. -/
def rjTwistEigen (b r N : ℕ) : RatFunc ℚ :=
  kinkScalar N / kinkScalar b ^ r

/-- The spectral idempotent `P_N = f_b^{⊗ r} L_N(c^r)` of the colour `N`, `L_N` the Lagrange
basis polynomial of the nodes `μ_M`, `M ∈ rjSpec b r`. -/
def rjIsoProj (b r N : ℕ) : SkMat (b * r) (b * r) :=
  rjColsProj b r *
    Polynomial.aeval (rjCycleMat b r ^ r) (Lagrange.basis (rjSpec b r) (rjTwistEigen b r) N)

/-- A pair of maps `(π, ι)` through a single bundle of `N` strands. -/
abbrev RJFusionPair (M : ℕ) : Type :=
  Σ N : ℕ, SkMat M N × SkMat N M

/-- The inductive invariant of RA2: a family of pairs `(π_x, ι_x)` through `f_(N_x)` whose sum
`∑ π_x ι_x` is `f_b^{⊗ r}`, each colour in the spectrum, each map natural, absorbing the
projectors, and an eigenvector of `c^r` (on the left for `π_x`, on the right for `ι_x`) with the
eigenvalue `μ_(N_x)`. -/
def RJGoodFamily (b r : ℕ) (L : List (RJFusionPair (b * r))) : Prop :=
  (L.map fun x ↦ x.2.1 * x.2.2).sum = rjColsProj b r ∧
    ∀ x ∈ L, x.1 ∈ rjSpec b r ∧ RJNat x.2.1 ∧ RJNat x.2.2 ∧
      rjColsProj b r * x.2.1 = x.2.1 ∧ x.2.1 * jwAt x.1 0 x.1 = x.2.1 ∧
      jwAt x.1 0 x.1 * x.2.2 = x.2.2 ∧ x.2.2 * rjColsProj b r = x.2.2 ∧
      rjCycleMat b r ^ r * x.2.1 = rjTwistEigen b r x.1 • x.2.1 ∧
      x.2.2 * rjCycleMat b r ^ r = rjTwistEigen b r x.1 • x.2.2

/-! ### RA5: the axis loop, the Hopf scalar, the trace of `c` on an isotypic part -/

/-- A bundle of `k` strands carrying the operator `Y`, encircling a bundle of `m` strands once
(the full twist, closed on the `k` strands). -/
def rjLoopWith (m k : ℕ) (Y : SkMat k k) : SkMat m m :=
  ptrTail m (m + k) (rjFullTwist m k * skPlace (m + k) (m + k) m Y)

/-- The axis loop: a loop coloured by `f_k` encircling a bundle of `m` strands. -/
def rjAxisLoop (m k : ℕ) : SkMat m m :=
  rjLoopWith m k (jwAt k 0 k)

/-- The Hopf scalar `(-1)^k [(N+1)(k+1)] / [N+1]` of a `k`-coloured loop around `f_N`. -/
def rjHopf (N k : ℕ) : RatFunc ℚ :=
  (-1) ^ k * quantumInt (((N : ℤ) + 1) * ((k : ℤ) + 1)) / quantumInt ((N : ℤ) + 1)

/-- The trace of the cabled cyclic braid on the isotypic part of colour `N` (Rosso–Jones, for
even `b = 2n`): `t^(4ri²+4i) [2ri+1] / θ_b` if `N + 1 = |2ri+1|` with `|i| ≤ n`, and `0` if `N` is
of no such form. -/
def rjCycleValue (b r N : ℕ) : RatFunc ℚ :=
  ∑ i ∈ Finset.Icc (-((b / 2 : ℕ) : ℤ)) ((b / 2 : ℕ) : ℤ),
    if (2 * (r : ℤ) * i + 1).natAbs = N + 1 then
      RatFunc.X ^ (4 * (r : ℤ) * i ^ 2 + 4 * i) * quantumInt (2 * (r : ℤ) * i + 1) / kinkScalar b
    else 0

/-! ### RA5: coloured closures of braids with a thickness profile -/

/-- The projectors `f_(κ x)` on the columns `x < n` of a profile `κ`, inside `V^{⊗ N}`. -/
def rjProfileProj (N : ℕ) (κ : ℕ → ℕ) (n : ℕ) : SkMat N N :=
  ((List.range n).map fun x ↦ jwAt N (profileOffset κ x) (κ x)).prod

/-- The coloured closure of a braid word on `n` strands whose column `x` is a bundle of `κ x`
strands carrying `f_(κ x)`: the quantum trace of the profile cable with all column projectors. -/
def rjColorTrace (κ : ℕ → ℕ) (n : ℕ) (w : BraidWord) : RatFunc ℚ :=
  qtr (profileOffset κ n)
    (braidMatrix (profileOffset κ n) (thickCable κ w) * rjProfileProj (profileOffset κ n) κ n)

/-- Two braid words on `n` strands are *equal for every profile*: their profile cables have the
same matrix whenever the bundles fit, and they permute the columns alike. -/
def RJBraidEq (n : ℕ) (w w' : BraidWord) : Prop :=
  IsOnStrands n w ∧ IsOnStrands n w' ∧
    ∀ (κ : ℕ → ℕ) (N : ℕ), profileOffset κ n ≤ N →
      braidMatrix N (thickCable κ w) = braidMatrix N (thickCable κ w') ∧
        profileEnd κ w = profileEnd κ w'

/-- The full twist of the strand `m` around the strands `0, …, m-1`:
`σ_(m-1) ⋯ σ_0 σ_0 ⋯ σ_(m-1)`. -/
def rjAxisWord : ℕ → BraidWord
  | 0 => []
  | m + 1 => (m, true) :: (rjAxisWord m ++ [(m, true)])

/-- The word `σ_(m-1)^(2p) · (σ_(m-1) ⋯ σ_0 σ_0 ⋯ σ_(m-1)) · (σ_0 ⋯ σ_(m-2))` on `m + 1` strands:
its closure, with the strands `0, …, m-1` forming one component (the closure of the cyclic
braid) and the strand `m` the axis, is the torus link `T(2, 2(m+p))`. -/
def rjBetaWord (m p : ℕ) : BraidWord :=
  List.replicate (2 * p) (m - 1, true) ++ rjAxisWord m ++ rjCycleWord m

/-- The profile of `m` bundles of `b` strands followed by bundles of `k` strands. -/
def rjAxisProfile (b k m : ℕ) : ℕ → ℕ :=
  fun x ↦ if x < m then b else k

/-! ### RA4: the field embedding `t ↦ t^r` -/

/-- The embedding `ℚ(t) → ℚ(t)`, `t ↦ t^r` (for `r ≥ 1`; `t ↦ t` for `r = 0`). In the target,
`t^(1/r)` exists, so that the eigenvalues of the cyclic braid on an isotypic part acquire `r`-th
roots. -/
def rjEmbed (r : ℕ) : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.mapRingHom (Polynomial.expand ℚ (max r 1)) (by
    intro p hp
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero] at *
    intro h
    apply hp
    exact Polynomial.expand_injective (lt_of_lt_of_le Nat.one_pos (le_max_right r 1))
      (by simpa using h))

/-- The `r`-th root `ν_N = t^(N(N+2)) / θ_b` (in the target of `rjEmbed r`) of the eigenvalue
`μ_N` of `c^r`, for even `b` and `N`. -/
def rjNu (b r N : ℕ) : RatFunc ℚ :=
  RatFunc.X ^ (N * (N + 2)) / rjEmbed r (kinkScalar b)

end AJConjecture
