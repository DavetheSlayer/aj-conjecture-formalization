import Mathlib
import AJHandoff.Geometry.GeoZhEq519
import AJHandoff.Geometry.GeoPhysDiagonal

/-!
# G-PHYS conditional only on Zheng's estimates as printed

`ZhengEstimates a` contains two estimates, (5.16) and (5.19), that involve the logarithmic
derivative `b_{n,i}`, whose sign is corrected in `geoZhengB`. Both are now derived:
(5.16) unconditionally (`zhengEq516_holds`), and (5.19) from Zheng's `b`-free bound (5.12)
(`zhengEq519_of_zhengEq512`). What remains cited is exactly Zheng's printed statements, none of
which involves `b`: Lemma 3.2, Lemma 3.3 (with the constant (3.34)), (5.12), (5.20) and
Proposition 4.1 (`ZhengVerbatim a`).
-/

open Filter Topology

noncomputable section

namespace AJConjecture

/-- Zheng's analytic inputs for the companion `T(a, 2)` exactly as printed in math/0508138v4
(none involves `b_{n,i}`): Lemma 3.2; Lemma 3.3 for `β = -(8a+1)` and `β = 0`; (5.12); (5.20);
Proposition 4.1. -/
def ZhengVerbatim (a : ℕ) : Prop :=
  ZhengLemma32 ∧
    (∀ δ : ℝ, 1 / 2 < δ → δ < 2 / 3 →
      ZhengLemma33 (-(8 * a + 1 : ℝ)) δ ∧ ZhengLemma33 0 δ) ∧
    ZhengEq512 a ∧ ZhengEq520 a ∧ ZhengProp41 a

/-- The printed estimates imply the estimates used, with (5.16), (5.19) for the corrected `b`. -/
theorem zhengEstimates_of_verbatim (a : ℕ) (ha : 1 ≤ a) (h : ZhengVerbatim a) :
    ZhengEstimates a :=
  ⟨h.1, h.2.1, zhengEq516_holds a, zhengEq519_of_zhengEq512 a ha h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- G-PHYS conditional only on Zheng's printed (`b`-free) estimates: the diagonal at `q_N` is
asymptotic to the nonzero leading term. -/
theorem geo_phys_of_zhengVerbatim (a : ℕ) (ha : 3 ≤ a) (hodd : Odd a) (hZ : ZhengVerbatim a) :
    (∀ N : ℕ, 1 ≤ N → geoZhengLeading a N ≠ 0) ∧
      Tendsto (fun N : ℕ ↦ geoZhengDiagonal a N / geoZhengLeading a N) atTop (𝓝 1) :=
  have h := geo_phys_diagonal a ha hodd (zhengEstimates_of_verbatim a (by omega) hZ)
  ⟨h.2.2.1, h.2.2.2.2⟩

end AJConjecture
