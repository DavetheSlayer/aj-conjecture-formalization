import Mathlib
import AJFamily.Classical.FamilyPeripheralGaps
import AJFamily.Classical.FamilyPeripheralStrandLoop
import AJFamily.Skein.TorusWordWrithe
import AJFamily.Skein.WhiteheadTorusKnot

/-!
# The satellite structure of the family knots

The knot group of `whiteheadTorusKnot k` carries the satellite structure of the Whitehead double
of `T(2, 2k+1)` with its meridian and preferred longitude. The relations of
`isSatelliteData_of_famRelations` are supplied by the closed forms of the gap products, the
Hopf-clasp loops and the edge meridians of the block list `famBlocks k`, and by the longitude
formula `map_longitude_blocks`.
-/

namespace AJConjecture

theorem satellitePeripheral_whiteheadTorusKnot (k : ℕ) (hk : 1 ≤ k) :
    SatellitePeripheral (whiteheadTorusKnot k hk) k := by
  have hw : (whiteheadTorusKnot k hk).word = blocksWord (famBlocks k) :=
    (blocksWord_famBlocks k).symm
  have hv : ∀ b ∈ famBlocks k, b.Valid (whiteheadTorusKnot k hk).strands := famBlocks_valid k hk
  have horb : (stPerm (famBlocks k))^[(whiteheadTorusKnot k hk).strands] 0 = 0 :=
    iterate_stPerm_famBlocks_period k hk
  let ρ := MonoidHom.id (KnotGroup (whiteheadTorusKnot k hk))
  let f : Fin (4 * k + 3) → KnotGroup (whiteheadTorusKnot k hk) := fun t ↦ PresentedGroup.of t
  let L : ℕ → KnotGroup (whiteheadTorusKnot k hk) := loopAt (4 * k + 3) (famBlocks k) f
  have hgap : ∀ n, gapProd (4 * k + 3) (famBlocks k) f n = 1 := fun n ↦
    gapProd_fixed (whiteheadTorusKnot k hk) (famBlocks k) hw hv ρ n
  have hedge : ∀ t, t < 4 * k + 3 → edgeMer f t =
      stLoop (4 * k + 3) (famBlocks k) f t * edgeMer f (stPerm (famBlocks k) t) *
        (stLoop (4 * k + 3) (famBlocks k) f t)⁻¹ := fun t ht ↦
    edgeMer_fixed (whiteheadTorusKnot k hk) (famBlocks k) hw hv ρ t ht
  obtain ⟨hlon, hcomm⟩ := map_longitude_blocks (whiteheadTorusKnot k hk) (famBlocks k) hw hv horb ρ
  change longitude _ = meridian _ ^ orbitCount (4 * k + 3) (famBlocks k) *
      orbitLoop (4 * k + 3) (famBlocks k) f * meridian _ ^ (-(writhe (whiteheadTorusWord k))) at hlon
  change orbitLoop (4 * k + 3) (famBlocks k) f * meridian _ =
      meridian _ * orbitLoop (4 * k + 3) (famBlocks k) f at hcomm
  rw [orbitCount_famBlocks k hk, writhe_whiteheadTorusWord k hk, orbitLoop_famBlocks k hk] at hlon
  rw [orbitLoop_famBlocks k hk] at hcomm
  have hmer : meridian (whiteheadTorusKnot k hk) = edgeMer f 0 := by
    rw [edgeMer_zero f (by omega)]; rfl
  refine ⟨_, _, isSatelliteData_of_famRelations k hk L (meridian _) (edgeMer f (4 * k + 2))
    (edgeMer f (4 * k + 1)) (longitude _) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcomm⟩
  · intro n h1 h2
    rw [← gapProd_famBlocks_climb k hk f n h1 h2]; exact hgap n
  · rw [← gapProd_famBlocks_bigClimb k hk f]; exact hgap _
  · rw [← gapProd_famBlocks_close k hk f]; exact hgap _
  · intro n h1 h2
    rw [← gapProd_famBlocks_stair k hk f n h1 h2]; exact hgap n
  · rw [← gapProd_famBlocks_firstStep k hk f]; exact hgap _
  · rw [← gapProd_famBlocks_clasp k hk f]; exact hgap _
  · rw [← gapProd_famBlocks_hopf k hk f]; exact hgap _
  · exact loopAt_famBlocks_hopf1 k hk f
  · exact loopAt_famBlocks_hopf2 k hk f
  · have h := hedge 0 (by omega)
    rw [stLoop_famBlocks k hk f 0 (by omega), stPerm_famBlocks k hk 0 (by omega)] at h
    rw [hmer]; simpa [whiteheadTorusPermNat] using h
  · have h := hedge (4 * k + 2) (by omega)
    rw [stLoop_famBlocks k hk f _ (by omega), stPerm_famBlocks k hk _ (by omega)] at h
    have hp : whiteheadTorusPermNat k (4 * k + 2) = 0 := by
      unfold whiteheadTorusPermNat; split_ifs <;> omega
    rw [hp, ← hmer] at h; exact h
  · rw [hlon]

end AJConjecture
