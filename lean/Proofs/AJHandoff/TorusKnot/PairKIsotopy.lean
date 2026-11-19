import Mathlib
import AJHandoff.TorusKnot.PairKIsoFinal
import AJHandoff.TorusKnot.PairKKnot
import AJFamily.Skein.TorusPhaseOne
import AJFamily.Skein.TorusPhaseTwo

/-!
# The isotopy from the braided-surface word to the satellite diagram (crux)

`morseReach_pair_source_target`: the long closure of `pairWhiteheadWord r s` reaches the
band-and-clasp target word `pairTargetWord r s` by the checked moves of `AJConjecture.MorseRule`.
Both words have writhe `2(r - 1)s - 2`.

* `r = 2` (`s = 2k + 1`): the library's isotopy, `morseReach_source_strip` and
  `morseReach_strip_target` (`AJFamily.Skein.TorusPhaseOne`, `TorusPhaseTwo`), through
  `pairWhiteheadWord_two`, `pairStrands_two` and `pairTargetWord_two`.
* `r ≥ 3`: `morseReach_pair_source_target_ge3` (`AJHandoff.TorusKnot.PairKIsoFinal`): generic
  thinning and dead-end retraction (phase I, `PairKIsoThin`, `PairKIsoDeadEnd`), the strip word in
  closed form (`PairKIsoStrip`), the normal form of the strip blocks (stage N), the swing of the
  return strand (stage S), the clasp (stage P), the bead stages C, G, E, and the companion isotopy
  on one strand lifted by doubling. Plan, words and checks: `SCR/ISO/DESIGN.md`.

The statement is unchanged from the previous scaffold; `longKnotOp_pairWhiteheadKnot`
(`PairKLongKnot`) is proved from it by soundness of the checker.
-/

namespace AJConjecture

/-- Crux of T-KNOT: the closed braid `pairWhiteheadWord r s`, cut open in its first column,
reaches the band-and-clasp diagram of `Wh⁻₀(T(r, s))`. -/
theorem morseReach_pair_source_target {r s : ℕ} (h : IsTorusPair r s) :
    MorseReach 1 (morseLongClosure (pairStrands r s) (pairWhiteheadWord r s))
      (pairTargetWord r s) := by
  obtain ⟨hr, hrs, hcop⟩ := h
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  · -- `r = 2`: the library's isotopy
    obtain rfl : r = 2 := by omega
    have hodd : s % 2 = 1 := by
      rcases Nat.even_or_odd s with ⟨m, hm⟩ | ⟨m, hm⟩
      · exfalso
        have h2 : 2 ∣ Nat.gcd 2 s := Nat.dvd_gcd (dvd_refl 2) ⟨m, by omega⟩
        rw [hcop] at h2
        omega
      · omega
    obtain ⟨k, rfl⟩ : ∃ k, s = 2 * k + 1 := ⟨s / 2, by omega⟩
    have hk : 1 ≤ k := by omega
    rw [pairStrands_two, pairWhiteheadWord_two k hk, pairTargetWord_two k]
    exact morseReach_trans (morseReach_source_strip k hk) (morseReach_strip_target k hk)
  · exact morseReach_pair_source_target_ge3 ⟨hr, hrs, hcop⟩ hr3

end AJConjecture
