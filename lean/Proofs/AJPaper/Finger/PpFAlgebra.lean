import Mathlib
import AJPaper.Finger.PpFDefs

/-!
# Algebra of the extra support (Unit PpF, node `PpF_Algebra`)

General properties of `IsExtraSupport f A Δ` ("`Δ = 𝖫(f) / gcd(𝖫(f), A)`", eq. (45) of the
paper), in a commutative ring.

* `isExtraSupport_congr`: the predicate only depends on `f`, `A`, `Δ` up to association.
* `isExtraSupport_prime_dvd`: a prime dividing `f` and not `A` divides `Δ` ("`Δ_K` records the
  irreducible factors that occur on the quantum side and are absent from the classical side").
* `isExtraSupport_of_three_primes`: the model of the trefoil test: for pairwise non-associated
  primes `l`, `G`, `B`, if `f ≐ l² G B` and `A ≐ l B` then `Δ ≐ G` (with `S = l G B`,
  `g = l B`; `l G B` is square-free because the three primes are pairwise non-associated).
* `isExtraSupport_map_of_involutive`: transport along an involutive ring endomorphism (used for
  the meridian inversion `ρ` of Section 9: "`Δ_{K^*} ≐ ρ(Δ_K)`").
-/

open Polynomial

noncomputable section

namespace AJConjecture

/-- A square-free part only depends on its arguments up to association. -/
private theorem isSquarefreePart_congr_ppfAlgebra {R : Type*} [CommMonoidWithZero R]
    {f f' S S' : R} (hf : Associated f f') (hS : Associated S S') (h : IsSquarefreePart f S) :
    IsSquarefreePart f' S' :=
  ⟨fun y hy ↦ h.1 y (hy.trans hS.symm.dvd), fun g hg ↦
    ⟨fun hgS ↦ (((h.2 g hg).1 (hgS.trans hS.symm.dvd))).trans hf.dvd,
      fun hgf ↦ ((h.2 g hg).2 (hgf.trans hf.symm.dvd)).trans hS.dvd⟩⟩

/-- The extra support only depends on its arguments up to association. -/
theorem isExtraSupport_congr {R : Type*} [CommMonoidWithZero R] {f f' A A' Δ Δ' : R}
    (hf : Associated f f') (hA : Associated A A') (hΔ : Associated Δ Δ')
    (h : IsExtraSupport f A Δ) : IsExtraSupport f' A' Δ' := by
  obtain ⟨S, g, hS, ⟨hgS, hgA, hgcd⟩, rfl⟩ := h
  have hSS : Associated (g * Δ) (g * Δ') := hΔ.mul_left g
  exact ⟨g * Δ', g, isSquarefreePart_congr_ppfAlgebra hf hSS hS,
    ⟨dvd_mul_right g Δ', hgA.trans hA.dvd, fun d hdS hdA ↦
      hgcd d (hdS.trans hSS.symm.dvd) (hdA.trans hA.symm.dvd)⟩, rfl⟩

/-- A prime dividing `f` and not dividing `A` divides the extra support. -/
theorem isExtraSupport_prime_dvd {R : Type*} [CommMonoidWithZero R] {f A Δ G : R}
    (hG : Prime G) (hf : G ∣ f) (hA : ¬ G ∣ A) (h : IsExtraSupport f A Δ) : G ∣ Δ := by
  obtain ⟨S, g, hS, ⟨-, hgA, -⟩, rfl⟩ := h
  exact (hG.dvd_or_dvd ((hS.2 G hG).2 hf)).resolve_left fun hGg ↦ hA (hGg.trans hgA)

/-- The product of a prime and a square-free element that it does not divide is square-free. -/
private theorem squarefree_prime_mul_ppfAlgebra {R : Type*} [CommRing R] [IsDomain R] {p x : R}
    (hp : Prime p) (hpx : ¬ p ∣ x) (hx : Squarefree x) : Squarefree (p * x) := by
  rintro y ⟨c, hc⟩
  have hpy : ¬ p ∣ y := by
    rintro ⟨z, rfl⟩
    refine hpx ⟨z * z * c, mul_left_cancel₀ hp.ne_zero ?_⟩
    rw [hc]
    ring
  obtain ⟨c', rfl⟩ : p ∣ c := by
    have hdvd : p ∣ y * y * c := ⟨x, hc.symm⟩
    exact (hp.dvd_or_dvd hdvd).resolve_left fun hyy ↦ hpy ((hp.dvd_or_dvd hyy).elim id id)
  refine hx y ⟨c', mul_left_cancel₀ hp.ne_zero ?_⟩
  rw [hc]
  ring

/-- The model computation: `f ≐ l² G B` and `A ≐ l B` with pairwise non-associated primes give
`Δ ≐ G`. -/
theorem isExtraSupport_of_three_primes {R : Type*} [CommRing R] [IsDomain R] {f A l G B : R}
    (hl : Prime l) (hG : Prime G) (hB : Prime B) (hlG : ¬ l ∣ G) (hlB : ¬ l ∣ B)
    (hGB : ¬ G ∣ B) (hf : Associated f (l ^ 2 * G * B)) (hA : Associated A (l * B)) :
    IsExtraSupport f A G := by
  have hlGB : ¬ l ∣ G * B := fun hd ↦ (hl.dvd_or_dvd hd).elim hlG hlB
  have hsq : Squarefree (l * (G * B)) :=
    squarefree_prime_mul_ppfAlgebra hl hlGB
      (squarefree_prime_mul_ppfAlgebra hG hGB hB.irreducible.squarefree)
  refine ⟨l * (G * B), l * B, ⟨hsq, fun p hp ↦ ?_⟩,
    ⟨⟨G, by ring⟩, hA.symm.dvd, fun d _ hdA ↦ hdA.trans hA.dvd⟩, by ring⟩
  rw [hf.dvd_iff_dvd_right]
  simp only [hp.dvd_mul, hp.dvd_pow_iff_dvd two_ne_zero, or_assoc]

/-- Transport of the extra support along an involutive ring endomorphism. -/
theorem isExtraSupport_map_of_involutive {R : Type*} [CommRing R] (φ : R →+* R)
    (hφ : Function.Involutive φ) {f A Δ : R} (h : IsExtraSupport f A Δ) :
    IsExtraSupport (φ f) (φ A) (φ Δ) := by
  obtain ⟨S, g, hS, ⟨hgS, hgA, hgcd⟩, rfl⟩ := h
  have hdvd : ∀ {a b : R}, a ∣ φ b → φ a ∣ b := fun {a b} hab ↦ by
    simpa only [hφ b] using map_dvd φ hab
  have hprime : ∀ {p : R}, Prime p → Prime (φ p) := fun {p} hp ↦
    (MulEquiv.prime_iff (RingEquiv.ofRingHom φ φ (RingHom.ext hφ) (RingHom.ext hφ))).2 hp
  refine ⟨φ (g * Δ), φ g, ⟨fun y hy ↦ ?_, fun p hp ↦ ⟨fun hpS ↦ ?_, fun hpf ↦ ?_⟩⟩,
    ⟨map_dvd φ hgS, map_dvd φ hgA, fun d hdS hdA ↦ ?_⟩, map_mul φ g Δ⟩
  · have hy' : φ y * φ y ∣ g * Δ := by
      rw [← map_mul]
      exact hdvd hy
    simpa only [hφ y] using (hS.1 (φ y) hy').map φ
  · simpa only [hφ p] using map_dvd φ ((hS.2 (φ p) (hprime hp)).1 (hdvd hpS))
  · simpa only [hφ p] using map_dvd φ ((hS.2 (φ p) (hprime hp)).2 (hdvd hpf))
  · simpa only [hφ d] using map_dvd φ (hgcd (φ d) (hdvd hdS) (hdvd hdA))

end AJConjecture
