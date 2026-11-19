import Mathlib
import AJConjecture.QAlgTransferJetData

/-!
# The Lucas sequences commute with ring homomorphisms

`transferLucas`, `transferLucasDeriv` and `transferLucasHasse` are polynomial expressions in their
arguments, so `f (F z s d) = F (f z) (f s) d` for a ring homomorphism `f` (induction on `d`).
-/

namespace AJConjecture

/-- The Lucas sequence commutes with ring homomorphisms. -/
theorem map_transferLucas {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z s : R) :
    ∀ d : ℕ, f (transferLucas z s d) = transferLucas (f z) (f s) d
  | 0 => by rw [transferLucas, transferLucas, map_ofNat]
  | 1 => by rw [transferLucas, transferLucas]
  | d + 2 => by
    rw [transferLucas, transferLucas, map_sub, map_mul, map_mul, map_transferLucas f z s (d + 1),
      map_transferLucas f z s d]

/-- The derivative of the Lucas sequence commutes with ring homomorphisms. -/
theorem map_transferLucasDeriv {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z s : R) :
    ∀ d : ℕ, f (transferLucasDeriv z s d) = transferLucasDeriv (f z) (f s) d
  | 0 => by rw [transferLucasDeriv, transferLucasDeriv, map_zero]
  | 1 => by rw [transferLucasDeriv, transferLucasDeriv, map_one]
  | d + 2 => by
    rw [transferLucasDeriv, transferLucasDeriv, map_sub, map_add, map_mul, map_mul,
      map_transferLucas, map_transferLucasDeriv f z s (d + 1), map_transferLucasDeriv f z s d]

/-- The second Hasse derivative of the Lucas sequence commutes with ring homomorphisms. -/
theorem map_transferLucasHasse {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z s : R) :
    ∀ d : ℕ, f (transferLucasHasse z s d) = transferLucasHasse (f z) (f s) d
  | 0 => by rw [transferLucasHasse, transferLucasHasse, map_zero]
  | 1 => by rw [transferLucasHasse, transferLucasHasse, map_zero]
  | d + 2 => by
    rw [transferLucasHasse, transferLucasHasse, map_sub, map_add, map_mul, map_mul,
      map_transferLucasDeriv, map_transferLucasHasse f z s (d + 1),
      map_transferLucasHasse f z s d]

end AJConjecture
