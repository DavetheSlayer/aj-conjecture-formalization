import Mathlib
import AJTwist.Knot.TwKBlocks

/-!
# The block words of the twisted doubles, as seen by the classical side (Unit C2)

The braids are those of package TwK (`AJTwist.Knot.TwKBlocks`): `twBlocks r s ℓ σ` is
`pairBlocks r s` with the head block `b(0, j₀)`, `j₀ = twHeadTop r s`, replaced by the chain
`twChain M j₀ ℓ` through `twExtra ℓ` new discs on the new top levels `M, M + 1, …`
(`M = 2c + 1`), and with Hopf letters of sign `σ`.

What Unit C2 uses of this definition:

1. every block and every level of `pairBlocks r s` other than the head block is kept
   (`twBlocks_eq_chain_append`: the list is the chain followed by the tail of
   `twcBase r s σ`, the untwisted list with clasp sign `σ`);
2. the chain is the first block: no block acts below it;
3. the blocks of the chain touch only the levels `0`, `j₀` and the new levels `≥ M`, and no
   other block touches a new level (`twcBase_valid`).

Under 1–3 the chamber products of the old levels see the chain as a band `b(0, j₀)` with a
different loop (`AJTwist.Classical.TwCChain`), and the theorems of
`AJHandoff.TorusKnot.PairKOrb*`, `PairKPeri*` about the run of `pairBlocks r s` on an arbitrary
tuple apply to a modified tuple (`AJTwist.Classical.TwCVirtual`).

A warning that belongs to the record (found while designing this unit, and found independently
by TwK): replacing a single-letter band `σ_i` by `|1 - 2ℓ|` letters on the same level is *not*
the `ℓ`-twisted double unless `ℓ ∈ {0, 1}`; for `(r, s) = (2, 3)` the closures have Alexander
polynomials `1` (`σ³`), `t² - t + 1` (`σ⁵`), `t⁴ - t³ + t² - t + 1` (`σ⁻³`, genus `2`)
(`SCR/C/py/v2_alex_poly.py`).

Checked by computer for `twBlocks` (`SCR/C/py/w1_twk_basic.py`): for
`(r, s) ∈ {(2,3), (2,5), (3,4), (3,5)}`, `|ℓ| ≤ 3`, both `σ`: one component, writhe
`2c - 2ℓ ∓ 2`, Alexander polynomial `ℓ t + (1 - 2ℓ) + ℓ t⁻¹` for `σ = true` (the mirror type for
`σ = false`).
-/

namespace AJConjecture

/-- `pairBlocks r s` with Hopf letters of sign `σ` (`σ = true`: the list itself). -/
def twcBase (r s : ℕ) (σ : Bool) : List SBlock := (pairBlocks r s).map (twClaspBlock σ)

/-- The negative-clasp base list is `pairBlocks r s`. -/
theorem twcBase_true (r s : ℕ) : twcBase r s true = pairBlocks r s := by
  refine (List.map_congr_left fun b _ ↦ ?_).trans (List.map_id _)
  cases b <;> rfl

/-- The base list starts with the head block `b(0, j₀)`. -/
theorem twcBase_eq_head_cons {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) :
    twcBase r s σ = SBlock.band 0 (twHeadTop r s) :: (twcBase r s σ).tail := by
  have hc : twcBase r s σ = SBlock.band 0 (twHeadTop r s) ::
      (pairBlocks r s).tail.map (twClaspBlock σ) := by
    conv_lhs => rw [twcBase, pairBlocks_eq_head_cons h]
    rfl
  rw [hc, List.tail_cons]

/-- The twisted list is the chain followed by the base list without its head block. -/
theorem twBlocks_eq_chain_append (r s : ℕ) (ℓ : ℤ) (σ : Bool) :
    twBlocks r s ℓ σ =
      twChain (pairStrands r s) (twHeadTop r s) ℓ ++ (twcBase r s σ).tail := by
  rw [twBlocks, twcBase, List.map_tail]

/-- The blocks of the base list live on the old `2c + 1` strands. -/
theorem twcBase_valid {r s : ℕ} (h : IsTorusPair r s) (σ : Bool) :
    ∀ b ∈ twcBase r s σ, b.Valid (pairStrands r s) := by
  intro b hb
  obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
  have hv := pairBlocks_valid h b' hb'
  cases b' with
  | band i j => exact hv
  | neg i =>
    have hT : i + 1 < pairStrands r s := hv
    cases σ
    · simp only [SBlock.Valid, twClaspBlock, Bool.false_eq_true, ite_false]
      omega
    · exact hv

/-- `0 < j₀ < 2c + 1`. -/
theorem twHeadTop_pos_lt {r s : ℕ} (h : IsTorusPair r s) :
    0 < twHeadTop r s ∧ twHeadTop r s < pairStrands r s := by
  have hv : (SBlock.band 0 (twHeadTop r s)).Valid (pairStrands r s) :=
    pairBlocks_valid h _ (by rw [pairBlocks_eq_head_cons h]; exact List.mem_cons_self)
  exact hv

end AJConjecture
