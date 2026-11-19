import Mathlib

/-!
# The extra-factor obstruction

A prime element that divides `f` but not `a` prevents `√(f) = (a)`. This is the commutative
core of a disproof of the square-free AJ statement: an irreducible factor of the specialised
recurrence polynomial that is missing from the A-polynomial.
-/

namespace AJConjecture

/-- If a prime `p` divides `f` but not `a`, then the radical of `(f)` is not `(a)`. -/
theorem radical_span_singleton_ne_of_prime_dvd {R : Type*} [CommRing R] {p f a : R}
    (hp : Prime p) (hf : p ∣ f) (ha : ¬ p ∣ a) :
    (Ideal.span {f}).radical ≠ Ideal.span {a} := by
  intro h
  have hmem : a ∈ (Ideal.span {f}).radical := h ▸ Ideal.mem_span_singleton_self a
  obtain ⟨n, hn⟩ := hmem
  rw [Ideal.mem_span_singleton] at hn
  exact ha (hp.dvd_of_dvd_pow (hf.trans hn))

end AJConjecture
