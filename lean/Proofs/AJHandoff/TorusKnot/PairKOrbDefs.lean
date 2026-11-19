import Mathlib
import AJHandoff.TorusKnot.PairKPeriComp

/-!
# The orbit split of `pairBlocks r s`: definitions

Notation (`c = (r - 1)s`, `T = 2c - 1`, `m = 2c + 1`, `b₀ = 2c - s - r`, `z = c - r - 1`).
The positions of `pairBlocks r s` fall into two blocks:

* the *bottom* block `[0, c - s] ∪ {2c}`: the low strands `0, …, r - 2` and `2c` (low index
  `r - 1`), and the decreasing run `[r - 1, c - s]`;
* the *top* block `[c - s + 1, T]` (`PairOrbTop`): the increasing run, the window
  `[b₀, b₀ + r - 1]` (whose last position `pairOrbH1 = 2c - s - 1` collects the first Hopf loop)
  and the staircase `[2c - s, T]`.

The orbit of `0` runs through the bottom block to `T`, through the whole top block to `pairOrbH1`,
jumps to `2c` and runs through the rest of the bottom block back to `0`.

In terms of the rounds `y_i = R_(i mod s)` (`pairOrbY`, an `s`-periodic sequence on `ℤ`) and the
common product `K = C⁻¹ A⁻¹ B⁻¹` of `r` consecutive rounds (`pairOrbK`), every strand loop except
those of `T` (which starts with the second Hopf loop) and of `pairOrbH1` is *pure* in the frame of
`y_0`: `y_0 S_t y_0⁻¹ = K ^ w(t) * y_(ℓ(P t)) ^ n(t)` (`pairOrbW`, `pairOrbN`, `pairOrbLab`), and
`ℓ(t) ≡ ℓ(P t) + r w(t) (mod s)`. Pure steps multiply along the orbit; the sums of `w` and `n`
over the two blocks are `s, -rs` (bottom) and `-s, rs` (top). This gives the orbit identities of
`AJHandoff.TorusKnot.PairKPeriOrbit` without enumerating the orbit.

The raw strand loops (`pairOrbCore`, in terms of the block loops `L q`) and the closed form of the
strand map (`pairOrbPerm`) are checked below with `#guard` against `stPerm` and the block positions
collected by `stLoop` (`stLoop_eq_prod_range`); the pure forms, the label congruences and the sums
were checked exactly in the torus knot group `⟨u, v | u^r = v^s⟩`
(`y_i = v^(ai) v^a u^(-b) v^(-ai)`, `K = v`, `ar - bs = 1`) for
`(r, s) ∈ {(2,3), (2,5), (2,7), (3,4), (3,5), (3,7), (3,8), (3,10), (4,5), (4,7), (4,9), (5,6),
(5,7), (5,8), (6,7), (7,9)}`.
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-! ### Positions -/

/-- The arithmetic of an admissible pair: `s ≤ c`, `r + 1 ≤ s` and `E + s + r = c + 3`
(`E = pairRunDown r s`), hence `r - 2 ≤ c - s`. -/
theorem pairOrb_arith {r s : ℕ} (h : IsTorusPair r s) :
    2 ≤ r ∧ r + 1 ≤ s ∧ s ≤ pairC r s ∧ pairRunDown r s + s + r = pairC r s + 3 := by
  obtain ⟨hr, hrs, -⟩ := h
  obtain ⟨a, rfl⟩ : ∃ a, r = a + 2 := ⟨r - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, s = b + 1 := ⟨s - 1, by omega⟩
  simp only [pairC, pairRunDown, Nat.add_sub_cancel]
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [show a + 2 - 1 = a + 1 by omega]
    nlinarith
  · rw [show a + 2 - 1 = a + 1 by omega]
    ring

/-- The window position `b₀ + r - 1 = 2c - s - 1`, whose strand collects the first Hopf loop. -/
def pairOrbH1 (r s : ℕ) : ℕ := 2 * pairC r s - s - 1

/-- The top block `[c - s + 1, T]` of positions. -/
abbrev PairOrbTop (r s t : ℕ) : Prop := pairC r s - s + 1 ≤ t ∧ t ≤ pairTop r s

/-- The low index of a low strand: `t` for `t ≤ r - 2`, `r - 1` for `t = 2c`. -/
def pairOrbLow (r s t : ℕ) : ℕ := if t = 2 * pairC r s then r - 1 else t

/-- The low index `(s + i) % r` that follows the low index `i`. -/
def pairOrbNext (r s i : ℕ) : ℕ := (s + i) % r

/-- The index of a foot position `b₀ + p` of the window: `p = t + s + r - 2c`. -/
def pairOrbFoot (r s t : ℕ) : ℕ := t + s + r - 2 * pairC r s

/-! ### The strand map -/

/-- The strand map `stPerm (pairBlocks r s)` in closed form: a low strand goes to the low strand
of the next low index (through the decreasing run when that index is `r - 2`, to `T` when it is
`r - 1`); the decreasing run steps down, the increasing run steps up, the window feet jump up by
`s`, `pairOrbH1` goes to `2c`, the bottom `2c - s` of the staircase to the foot `c - s + 1` of the
increasing run, and the staircase (with `T`) steps down by `r`. -/
def pairOrbPerm (r s t : ℕ) : ℕ :=
  if t + 2 ≤ r ∨ t = 2 * pairC r s then
    if pairOrbNext r s (pairOrbLow r s t) + 3 ≤ r then pairOrbNext r s (pairOrbLow r s t)
    else if pairOrbNext r s (pairOrbLow r s t) + 2 = r then pairC r s - s
    else pairTop r s
  else if t + s ≤ pairC r s then t - 1
  else if t + s + r < 2 * pairC r s then t + 1
  else if t + s + 2 ≤ 2 * pairC r s then t + s
  else if t + s + 1 = 2 * pairC r s then 2 * pairC r s
  else if t + s = 2 * pairC r s then pairC r s - s + 1
  else t - r

/-! ### Labels and exponents of the pure forms -/

/-- The label `ℓ(t)` of a position: `t + 1` on the low strands `t ≤ r - 2`, `r - 1` on the
decreasing and increasing runs and on `b₀`, `b₀ + r - 1 - t` on the window, `T - t` on the
staircase, `0` on `2c`. -/
def pairOrbLab (r s t : ℕ) : ℕ :=
  if t + 2 ≤ r then t + 1
  else if t + s + r ≤ 2 * pairC r s then r - 1
  else if t + s + 1 ≤ 2 * pairC r s then 2 * pairC r s - s - 1 - t
  else if t ≤ pairTop r s then pairTop r s - t
  else 0

/-- The power of `K` in the pure form of the low strand of low index `i`. -/
def pairOrbSlotW (r s i : ℕ) : ℤ :=
  if i + 1 = r then (((r - 1 + s) / r : ℕ) : ℤ) - 1
  else (((s + i) / r : ℕ) : ℤ) + if pairOrbNext r s i + 1 = r then 1 else 0

/-- The power of the round in the pure form of the low strand of low index `i`; the strand that
enters the decreasing run also collects the `z + 1 = c - r` run loops. -/
def pairOrbSlotN (r s i : ℕ) : ℤ :=
  -(pairOrbSlotW r s i + 1) -
    if pairOrbNext r s i + 2 = r then ((pairC r s - r : ℕ) : ℤ) else 0

/-- The power `w(t)` of `K` in the pure form of the strand loop of `t`. -/
def pairOrbW (r s t : ℕ) : ℤ :=
  if t + 2 ≤ r ∨ t = 2 * pairC r s then pairOrbSlotW r s (pairOrbLow r s t)
  else if t + s + 1 ≤ 2 * pairC r s then 0
  else -1

/-- The power `n(t)` of the round in the pure form of the strand loop of `t`. -/
def pairOrbN (r s t : ℕ) : ℤ :=
  if t + 2 ≤ r ∨ t = 2 * pairC r s then pairOrbSlotN r s (pairOrbLow r s t)
  else if t + s ≤ pairC r s then 0
  else if t + s + 1 ≤ 2 * pairC r s then 1
  else if t + s = 2 * pairC r s ∨ t = pairTop r s then 2
  else 1

/-! ### Rounds -/

/-- The rounds as an `s`-periodic sequence on `ℤ`: `y_i = R_(i mod s)`. -/
def pairOrbY (r s : ℕ) (L : ℕ → G) (i : ℤ) : G := L (pairIdxR r s (i % (s : ℤ)).toNat)

/-- The common product `K = C⁻¹ A⁻¹ B⁻¹` of `r` consecutive rounds. -/
def pairOrbK (r s : ℕ) (L : ℕ → G) : G :=
  (L (pairIdxC r s))⁻¹ * (descProd L 0 (r - 2))⁻¹ * (L (pairIdxB r s))⁻¹

/-- Conjugation by the round `y_0 = R_0`. -/
def pairOrbConj (r s : ℕ) (L : ℕ → G) (x : G) : G := pairOrbY r s L 0 * x * (pairOrbY r s L 0)⁻¹

/-! ### The raw strand loops -/

/-- The rounds collected by a low strand: `R_(s-1) ⋯ R_0` without the rounds `R_u`,
`u ≡ ρ (mod r)`. -/
def pairOrbSkip (r s : ℕ) (L : ℕ → G) (ρ : ℕ) : G :=
  ((List.range s).reverse.map fun u ↦ if u % r = ρ % r then 1 else L (pairIdxR r s u)).prod

/-- The tail of the loop of a low strand whose next low index is `j`: the left climbs
`A_j ⋯ A_0` for `j ≤ r - 3`; for `j = r - 2` the big climb, the increasing run, the first block of
the decreasing run and all left climbs; nothing for `j = r - 1`. -/
def pairOrbSuf (r s : ℕ) (L : ℕ → G) (j : ℕ) : G :=
  if j + 3 ≤ r then descProd L 0 (j + 1)
  else if j + 2 = r then
    L (pairIdxB r s) * descProd L (r - 2 + pairRunDown r s) (pairRunUp r s) * L (r - 2) *
      descProd L 0 (r - 2)
  else 1

/-- The loop of the low strand of low index `i`: the right descents `D'_(r-3) ⋯ D'_(r-2-i)`
(the top-right climb `C` for `i = r - 1`), the rounds without the residue class of `j + 1`, and
the tail (`j = (s + i) % r`). -/
def pairOrbSlotLoop (r s : ℕ) (L : ℕ → G) (i : ℕ) : G :=
  (if i + 1 = r then L (pairIdxC r s)
    else descProd (fun j ↦ L (pairIdxDp r s j)) (r - 2 - i) i) *
    pairOrbSkip r s L (pairOrbNext r s i + 1) * pairOrbSuf r s L (pairOrbNext r s i)

/-- The strand loop of the position `t`, in terms of the block loops `L q`, without the second
Hopf loop that the strand `T` collects first. -/
def pairOrbCore (r s : ℕ) (L : ℕ → G) (t : ℕ) : G :=
  if t + 2 ≤ r ∨ t = 2 * pairC r s then pairOrbSlotLoop r s L (pairOrbLow r s t)
  else if t + s ≤ pairC r s then
    descProd (fun j ↦ L (pairIdxDp r s j)) 0 (r - 2) * L (pairIdxR r s (s - 1)) *
      L (pairIdxRun r s t) * descProd L 0 (r - 2)
  else if t + s + r ≤ 2 * pairC r s then
    descProd (fun j ↦ L (pairIdxDp r s j)) 0 (r - 2) * L (pairIdxR r s (s - 1)) *
      descProd L 0 (r - 2)
  else if t + s + 2 ≤ 2 * pairC r s then
    descProd (fun j ↦ L (pairIdxDp r s j)) (pairOrbFoot r s t - 1) (r - 1 - pairOrbFoot r s t) *
      descProd L 0 (r - 2 - pairOrbFoot r s t)
  else if t + s + 1 = 2 * pairC r s then L (pairIdxH1 r s)
  else if t + s = 2 * pairC r s then
    L (pairIdxC r s) * L (pairIdxR r s (s - 1)) * descProd L 0 (r - 2)
  else if t + 1 < 2 * pairC r s then
    L (pairIdxC r s) * L (pairIdxR r s (pairTop r s - t)) * L (pairIdxB r s) * descProd L 0 (r - 2)
  else L (pairIdxR r s 0) * L (pairIdxB r s) * descProd L 0 (r - 2)

/-! ### The orbit of `0` -/

/-- The `k`-th strand `(stPerm (pairBlocks r s))^[k] 0` of the orbit of `0`. -/
def pairOrbT (r s k : ℕ) : ℕ := (stPerm (pairBlocks r s))^[k] 0

/-- The first index of the strand `t` on the orbit of `0`. -/
def pairOrbIdx (r s t : ℕ) : ℕ :=
  (List.range (pairStrands r s)).findIdx fun k ↦ decide (pairOrbT r s k = t)

/-- The product of the strand loops along the orbit of `0`, from the index `a` to `b - 1`. -/
def pairOrbSeg (r s : ℕ) (f : Fin (pairStrands r s) → G) (a b : ℕ) : G :=
  ((List.range (b - a)).map fun k ↦
    stLoop (pairStrands r s) (pairBlocks r s) f (pairOrbT r s (a + k))).prod

/-! ### Computational checks -/

section Checks

/-- The block positions collected by the strand at top position `t`, top to bottom (the
nontrivial factors of `stLoop_eq_prod_range`). -/
def pairOrbStLoopIdx (bs : List SBlock) (t : ℕ) : List ℕ :=
  (List.range bs.length).reverse.filter fun q ↦
    (bs.getD q (SBlock.neg 0)).carries (stPerm (bs.drop (q + 1)) t)

/-- The strand map is `pairOrbPerm` on all positions. -/
def pairOrbCheckPerm (r s : ℕ) : Bool :=
  (List.range (pairStrands r s)).all fun t ↦ stPerm (pairBlocks r s) t == pairOrbPerm r s t

/-- The strand loops, read on free generators for the block loops, are `pairOrbCore` (with the
second Hopf loop in front at `T`). -/
def pairOrbCheckLoop (r s : ℕ) : Bool :=
  (List.range (pairStrands r s)).all fun t ↦
    (((pairOrbStLoopIdx (pairBlocks r s) t).map fun q ↦ FreeGroup.of q).prod : FreeGroup ℕ) ==
      (if t = pairTop r s then FreeGroup.of (pairIdxH2 r s) else 1) *
        pairOrbCore r s (fun q ↦ FreeGroup.of q) t

/-- The label congruence `ℓ(t) ≡ ℓ(P t) + r w(t) (mod s)` off `pairOrbH1`. -/
def pairOrbCheckLab (r s : ℕ) : Bool :=
  (List.range (pairStrands r s)).all fun t ↦ t == pairOrbH1 r s ||
    ((pairOrbLab r s t : ℤ) - pairOrbLab r s (pairOrbPerm r s t) - r * pairOrbW r s t) % s == 0

/-- The sums of `w` and `n` over the top block (without `pairOrbH1`) and the bottom block. -/
def pairOrbCheckSums (r s : ℕ) : Bool :=
  let top := (List.range (pairStrands r s)).filter fun t ↦
    pairC r s - s + 1 ≤ t && t ≤ pairTop r s && t != pairOrbH1 r s
  let bot := (List.range (pairStrands r s)).filter fun t ↦
    t ≤ pairC r s - s || t == 2 * pairC r s
  (top.map (pairOrbW r s)).sum == -(s : ℤ) && (top.map (pairOrbN r s)).sum == ((r * s : ℕ) : ℤ) &&
    (bot.map (pairOrbW r s)).sum == (s : ℤ) && (bot.map (pairOrbN r s)).sum == -((r * s : ℕ) : ℤ)

/-- The orbit enters the top block at `T`, stays in it up to `pairOrbH1` and then jumps to `2c`;
outside these indices it is in the bottom block. -/
def pairOrbCheckOrder (r s : ℕ) : Bool :=
  let iT := pairOrbIdx r s (pairTop r s)
  let iH := pairOrbIdx r s (pairOrbH1 r s)
  iT < iH && pairOrbT r s (iH + 1) == 2 * pairC r s && iH + 1 < pairStrands r s &&
    (List.range (pairStrands r s)).all fun k ↦
      (decide (pairC r s - s + 1 ≤ pairOrbT r s k ∧ pairOrbT r s k ≤ pairTop r s)) ==
        (iT ≤ k && k ≤ iH)

#guard [(2, 3), (2, 5), (3, 4), (3, 5), (3, 7), (4, 5), (5, 7), (4, 9)].all fun p ↦
  pairOrbCheckPerm p.1 p.2 && pairOrbCheckLab p.1 p.2 && pairOrbCheckSums p.1 p.2 &&
    pairOrbCheckOrder p.1 p.2

#guard [(2, 5), (3, 4), (3, 5), (4, 5), (5, 7)].all fun p ↦ pairOrbCheckLoop p.1 p.2

end Checks

end AJConjecture
