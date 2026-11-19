import Mathlib
import AJTwist.Exist.TwHGaussUp
import AJTwist.Exist.TwHGaussDown

/-!
# Every Gaussian period lies in the span of a window of `2|ℓ| + 1` consecutive periods

`twHSpan_gauss`: if the periods `𝔊^(c)`, `c₀ ≤ c ≤ c₀ + 2|ℓ|`, lie in a saturated span, then
every period `𝔊^(c)`, `c ∈ ℤ`, does. Strong induction upwards from the window with
`twHSpan_gauss_up` and downwards with `twHSpan_gauss_down` (`twH_window_induction`, a statement
about predicates on `ℤ`).
-/

noncomputable section

namespace AJConjecture

/-- Window induction on `ℤ`: a predicate that holds on `w` consecutive integers and propagates
from any `w` consecutive integers to the next one above and to the next one below holds
everywhere. -/
theorem twH_window_induction (P : ℤ → Prop) (w : ℕ) (c₀ : ℤ)
    (hwin : ∀ c : ℤ, c₀ ≤ c → c < c₀ + w → P c)
    (hup : ∀ e : ℤ, (∀ c : ℤ, e - w ≤ c → c ≤ e - 1 → P c) → P e)
    (hdown : ∀ e : ℤ, (∀ c : ℤ, e + 1 ≤ c → c ≤ e + w → P c) → P e) (c : ℤ) : P c := by
  have hU : ∀ (n : ℕ) (c : ℤ), c₀ ≤ c → c < c₀ + w + n → P c := by
    intro n
    induction n with
    | zero =>
      intro c h1 h2
      exact hwin c h1 (by omega)
    | succ n ih =>
      intro c h1 h2
      rcases lt_or_ge c (c₀ + w + n) with h3 | h3
      · exact ih c h1 h3
      · exact hup c fun c' h4 h5 ↦ ih c' (by omega) (by omega)
  have hD : ∀ (n : ℕ) (c : ℤ), c₀ - n ≤ c → P c := by
    intro n
    induction n with
    | zero =>
      intro c h1
      exact hU ((c - c₀).toNat + 1) c (by omega) (by omega)
    | succ n ih =>
      intro c h1
      rcases le_or_gt (c₀ - n) c with h3 | h3
      · exact ih c h3
      · exact hdown c fun c' h4 _ ↦ ih c' (by omega)
  exact hD (c₀ - c).toNat c (by omega)

/-- Every Gaussian period lies in a saturated span that contains a window of `2|ℓ| + 1`
consecutive periods. -/
theorem twHSpan_gauss {ι : Type*} [Fintype ι] (g : ι → ℕ → RatFunc ℚ) (ℓ c₀ : ℤ)
    (hwin : ∀ c : ℤ, c₀ ≤ c → c ≤ c₀ + 2 * (ℓ.natAbs : ℤ) → TwHSpan g (twHGauss ℓ c)) (c : ℤ) :
    TwHSpan g (twHGauss ℓ c) := by
  have hw : ((2 * ℓ.natAbs + 1 : ℕ) : ℤ) = 2 * (ℓ.natAbs : ℤ) + 1 := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  refine twH_window_induction (fun c ↦ TwHSpan g (twHGauss ℓ c)) (2 * ℓ.natAbs + 1) c₀
    (fun c h1 h2 ↦ hwin c h1 (by rw [hw] at h2; omega))
    (fun e he ↦ twHSpan_gauss_up g ℓ e fun c h1 h2 ↦ he c (by rw [hw]; omega) h2)
    (fun e he ↦ twHSpan_gauss_down g ℓ e fun c h1 h2 ↦ he c h1 (by rw [hw]; omega)) c

end AJConjecture
