import Mathlib
import AJHandoff.Geometry.GeoZhVerbatim
import AJPaper.Zheng.PpZLemma32
import AJPaper.Zheng.PpZLemma33
import AJPaper.Zheng.PpZProp41
import AJPaper.Zheng.PpZEq512
import AJPaper.Zheng.PpZEq520

/-!
# Zheng's estimates and the unconditional physical diagonal (Unit PpZ, node `PpZ_Verbatim`)

Source: Theorem B.1 (4) of the paper (Appendix B.5, `sections/geometry.tex`, `sec:physical`),
which rests on H. Zheng, arXiv:math/0508138v4: Lemma 3.2, Lemma 3.3, (5.12), (5.20) and
Proposition 4.1 for the companion `T(a, 2)`.

* `zhengVerbatim_holds`: `ZhengVerbatim a` for odd `a ≥ 3`, from the five group theorems
  `zhengLemma32_holds`, `zhengLemma33_holds`, `zhengEq512_holds`, `zhengEq520_holds`,
  `zhengProp41_holds`. (`ZhengVerbatim 1` is false: `A⁺_{1,2}(N, 1) = 0`.)
* `geo_phys_holds`: the conclusion of `geo_phys_of_zhengVerbatim` with no analytic hypothesis:
  the diagonal `J_N(e^{2πi/N})` of Zheng's formula (5.3) is asymptotic to the nonzero leading term
  `geoZhengLeading a N`.
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- **Zheng's printed estimates hold** for the companion `T(a, 2)`, `a ≥ 3` odd. -/
theorem zhengVerbatim_holds (a : ℕ) (ha : 3 ≤ a) (hodd : Odd a) : ZhengVerbatim a :=
  ⟨zhengLemma32_holds,
    fun _ h1 h2 ↦ ⟨zhengLemma33_holds _ h1 h2, zhengLemma33_holds 0 h1 h2⟩,
    zhengEq512_holds a hodd, zhengEq520_holds a hodd, zhengProp41_holds a ha hodd⟩

/-- **Theorem B.1 (4), unconditionally**: the diagonal at `q_N = e^{2πi/N}` is asymptotic to the
nonzero leading term. -/
theorem geo_phys_holds (a : ℕ) (ha : 3 ≤ a) (hodd : Odd a) :
    (∀ N : ℕ, 1 ≤ N → geoZhengLeading a N ≠ 0) ∧
      Tendsto (fun N : ℕ ↦ geoZhengDiagonal a N / geoZhengLeading a N) atTop (𝓝 1) :=
  geo_phys_of_zhengVerbatim a ha hodd (zhengVerbatim_holds a ha hodd)

/-- **The estimates used by the diagonal theorems hold**: `ZhengEstimates a` (Zheng's estimates
with (5.16) and (5.19) for the corrected coefficient), the hypothesis of `geo_phys_diagonal` and
of the G-PHYS clause of `geo_theoremG`, for the companion `T(a, 2)`, `a ≥ 3` odd. -/
theorem zhengEstimates_holds (a : ℕ) (ha : 3 ≤ a) (hodd : Odd a) : ZhengEstimates a :=
  zhengEstimates_of_verbatim a (by omega) (zhengVerbatim_holds a ha hodd)

end AJConjecture
