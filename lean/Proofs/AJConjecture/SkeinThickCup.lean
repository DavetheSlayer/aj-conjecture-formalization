import Mathlib
import AJConjecture.SkeinPlaceComm
import AJConjecture.SkeinZigzag

/-!
# Thick cups and caps

The thick cup on `c + 1` strands is an outer cup with the thick cup on `c` strands nested
inside, and symmetrically for caps. Consequences, by induction on `c`: the thick zig-zag (a
bundle turned around twice is straight) and the value `δ^c` of `c` nested loops.
-/

namespace AJConjecture

/-- The entries of the thick cup on `c` strands nested at the position `1` of two strands. -/
private theorem skPlace_cupThick_apply_thickCup (c : ℕ) (m : Fin 2 → Bool)
    (b : Fin (2 * (c + 1)) → Bool) :
    skPlace 2 (2 * (c + 1)) 1 (cupThick c) m b =
      if m 0 = b ⟨0, by omega⟩ ∧ m 1 = b ⟨2 * c + 1, by omega⟩ then
        ∏ x : Fin c, cupEntry (b ⟨x + 1, by omega⟩) (b ⟨2 * c - x, by omega⟩)
      else 0 := by
  have hfit : 1 + 0 ≤ 2 ∧ 2 + 2 * c = 2 * (c + 1) + 0 := by omega
  simp only [skPlace, Matrix.of_apply, cupThick, hfit, and_self, ↓reduceDIte]
  refine if_congr ?_ ?_ rfl
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1 0 (by simp), (h2 1 (by simp)).trans ?_⟩
      congr 2
      simp only [Fin.val_one]
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
      · obtain rfl : x = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
        exact h1
      · obtain rfl : x = 1 := Fin.ext (by simp only [Fin.val_one]; omega)
        refine h2.trans ?_
        congr 2
        simp only [Fin.val_one]
        omega
  · refine Finset.prod_congr rfl fun x _ ↦ ?_
    congr 2 <;> (congr 1; omega)

/-- The entries of the thick cap on `c` strands nested at the position `1` of two strands. -/
private theorem skPlace_capThick_apply_thickCup (c : ℕ) (a : Fin (2 * (c + 1)) → Bool)
    (m : Fin 2 → Bool) :
    skPlace (2 * (c + 1)) 2 1 (capThick c) a m =
      if m 0 = a ⟨0, by omega⟩ ∧ m 1 = a ⟨2 * c + 1, by omega⟩ then
        ∏ x : Fin c, capEntry (a ⟨x + 1, by omega⟩) (a ⟨2 * c - x, by omega⟩)
      else 0 := by
  have hfit : 1 + 2 * c ≤ 2 * (c + 1) ∧ 2 * (c + 1) + 0 = 2 + 2 * c := by omega
  simp only [skPlace, Matrix.of_apply, capThick, hfit, and_self, ↓reduceDIte]
  refine if_congr ?_ ?_ rfl
  · constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(h1 ⟨0, by omega⟩ (by simp)).symm,
        ((h2 ⟨2 * c + 1, by omega⟩ (by simp; omega)).trans ?_).symm⟩
      congr 1
      ext
      simp
    · rintro ⟨h1, h2⟩
      refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
      · have hxv : (x : ℕ) = 0 := by omega
        exact (congrArg a (Fin.ext hxv)).trans (h1.symm.trans (congrArg m (Fin.ext hxv.symm)))
      · have hxv : (x : ℕ) = 2 * c + 1 := by omega
        refine (congrArg a (Fin.ext hxv)).trans (h2.symm.trans (congrArg m (Fin.ext ?_)))
        change (1 : ℕ) = (x : ℕ) + 0 - 2 * c
        omega
  · refine Finset.prod_congr rfl fun x _ ↦ ?_
    congr 2 <;> (congr 1; omega)

/-- A state of two factors is determined by its two values. -/
private theorem eq_vecCons_of_apply_thickCup (m : Fin 2 → Bool) (p q : Bool) (h0 : m 0 = p)
    (h1 : m 1 = q) : m = ![p, q] := by
  funext x
  fin_cases x
  · exact h0
  · exact h1

/-- The thick cup on `c + 1` strands: an outer cup, then the thick cup on `c` strands inside. -/
theorem cupThick_succ (c : ℕ) :
    cupThick (c + 1) = skCup * skPlace 2 (2 * (c + 1)) 1 (cupThick c) := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [skPlace_cupThick_apply_thickCup]
  rw [Fintype.sum_eq_single ![b ⟨0, by omega⟩, b ⟨2 * c + 1, by omega⟩]]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, and_self, ↓reduceIte, skCup, cupThick,
      Matrix.of_apply, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ]
    congr 1
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    congr 2
    congr 1
    omega
  · intro m hm
    have hne : ¬(m 0 = b ⟨0, by omega⟩ ∧ m 1 = b ⟨2 * c + 1, by omega⟩) := fun h ↦
      hm (eq_vecCons_of_apply_thickCup m _ _ h.1 h.2)
    simp only [hne, ↓reduceIte, mul_zero]

/-- The thick cap on `c + 1` strands: the thick cap on `c` strands inside, then an outer cap. -/
theorem capThick_succ (c : ℕ) :
    capThick (c + 1) = skPlace (2 * (c + 1)) 2 1 (capThick c) * skCap := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [skPlace_capThick_apply_thickCup]
  rw [Fintype.sum_eq_single ![a ⟨0, by omega⟩, a ⟨2 * c + 1, by omega⟩]]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, and_self, ↓reduceIte, skCap, capThick,
      Matrix.of_apply, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun x _ ↦ ?_
    congr 2
    congr 1
    omega
  · intro m hm
    have hne : ¬(m 0 = a ⟨0, by omega⟩ ∧ m 1 = a ⟨2 * c + 1, by omega⟩) := fun h ↦
      hm (eq_vecCons_of_apply_thickCup m _ _ h.1 h.2)
    simp only [hne, ↓reduceIte, zero_mul]

/-- The thick cup on no strands is the identity. -/
theorem cupThick_zero : cupThick 0 = (1 : SkMat 0 0) := by
  ext a b
  simp only [cupThick, Matrix.of_apply, Finset.univ_eq_empty, Finset.prod_empty, Matrix.one_apply,
    Subsingleton.elim a b, ↓reduceIte]

/-- The thick cap on no strands is the identity. -/
theorem capThick_zero : capThick 0 = (1 : SkMat 0 0) := by
  ext a b
  have hab : a = b := Subsingleton.elim (α := Fin 0 → Bool) a b
  simp only [capThick, Matrix.of_apply, Finset.univ_eq_empty, Finset.prod_empty, Matrix.one_apply,
    hab, ↓reduceIte]

/-- A placed thick cup on `c + 1` strands: the outer cup, then the thick cup on `c` strands. -/
theorem skPlace_cupThick_succ (n n' i c : ℕ) (h : i ≤ n)
    (h' : n + 2 * (c + 1) = n') :
    skPlace n n' i (cupThick (c + 1)) = cupAt n i * skPlace (n + 2) n' (i + 1) (cupThick c) := by
  rw [cupThick_succ, skPlace_mul n (n + 2) n' i skCup _ (by omega) (by omega) (by omega),
    skPlace_skPlace (n + 2) n' i 1 (cupThick c) (by omega) (by omega) (by omega) (by omega)]
  rfl

/-- A placed thick cap on `c + 1` strands: the thick cap on `c` strands, then the outer cap. -/
theorem skPlace_capThick_succ (n n' i c : ℕ) (h : i + 2 * (c + 1) ≤ n)
    (h' : n = n' + 2 * (c + 1)) :
    skPlace n n' i (capThick (c + 1)) = skPlace n (n' + 2) (i + 1) (capThick c) * capAt n' i := by
  rw [capThick_succ, skPlace_mul n (n' + 2) n' i _ skCap (by omega) (by omega) (by omega),
    skPlace_skPlace n (n' + 2) i 1 (capThick c) (by omega) (by omega) (by omega) (by omega)]
  rfl

/-- A placed thick cap on `c + 1` strands: the innermost cap, then the thick cap on `c`
strands. -/
theorem skPlace_capThick_succ_inner (c : ℕ) :
    ∀ m n' i : ℕ, i + 2 * c ≤ m → m = n' + 2 * c →
      skPlace (m + 2) n' i (capThick (c + 1)) = capAt m (i + c) * skPlace m n' i (capThick c) := by
  induction c with
  | zero =>
    intro m n' i h h'
    obtain rfl : m = n' := by omega
    rw [skPlace_capThick_succ (m + 2) m i 0 (by omega) (by omega), capThick_zero,
      skPlace_one (m + 2) (i + 1) 0 (by omega), skPlace_one m i 0 (by omega), Matrix.one_mul,
      Matrix.mul_one]
    rfl
  | succ c ih =>
    intro m n' i h h'
    rw [skPlace_capThick_succ (m + 2) n' i (c + 1) (by omega) (by omega),
      ih m (n' + 2) (i + 1) (by omega) (by omega), Matrix.mul_assoc,
      ← skPlace_capThick_succ m n' i c (by omega) (by omega), Nat.add_right_comm i 1 c,
      Nat.add_assoc i c 1]

/-- Thick zig-zag on the right with a free intermediate size. -/
private theorem cupThick_mul_capThick_right_thickCup (c : ℕ) :
    ∀ N : ℕ, N = 3 * c → skPlace c N c (cupThick c) * skPlace N c 0 (capThick c) = 1 := by
  induction c with
  | zero =>
    intro N hN
    obtain rfl : N = 0 := by omega
    have h1 : skPlace 0 0 0 (cupThick 0) = (1 : SkMat 0 0) := by
      rw [cupThick_zero]; exact skPlace_one 0 0 0 le_rfl
    have h2 : skPlace 0 0 0 (capThick 0) = (1 : SkMat 0 0) := by
      rw [capThick_zero]; exact skPlace_one 0 0 0 le_rfl
    rw [h1, h2, Matrix.mul_one]
  | succ c ih =>
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨3 * c + 1, by omega⟩
    have hcomm := skPlace_mul_skPlace_comm (c + 1 + 2) (c + 1) (M + 2) M c (c + 1 + 1) skCap
      (cupThick c) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [show c + 1 + 1 + 0 - 2 = c from by omega] at hcomm
    have hih := congrArg (skPlace (c + 1) (c + 1) 0) (ih (3 * c) rfl)
    rw [skPlace_mul (c + 1) M (c + 1) 0 _ _ (by omega) (by omega) (by omega),
      skPlace_skPlace (c + 1) M 0 c (cupThick c) (by omega) (by omega) (by omega) (by omega),
      skPlace_skPlace M (c + 1) 0 0 (capThick c) (by omega) (by omega) (by omega) (by omega),
      skPlace_one (c + 1) 0 c (by omega), Nat.zero_add, Nat.add_zero] at hih
    rw [skPlace_cupThick_succ (c + 1) (M + 2) (c + 1) c le_rfl (by omega),
      skPlace_capThick_succ_inner c M (c + 1) 0 (by omega) (by omega), Nat.zero_add,
      Matrix.mul_assoc, ← Matrix.mul_assoc (skPlace (c + 1 + 2) (M + 2) (c + 1 + 1) (cupThick c)),
      capAt, ← hcomm, Matrix.mul_assoc, hih, Matrix.mul_one]
    exact cupAt_succ_mul_capAt (c + 1) c (by omega)

/-- Thick zig-zag on the left with a free intermediate size. -/
private theorem cupThick_mul_capThick_left_thickCup (c : ℕ) :
    ∀ N : ℕ, N = 3 * c → skPlace c N 0 (cupThick c) * skPlace N c c (capThick c) = 1 := by
  induction c with
  | zero =>
    intro N hN
    obtain rfl : N = 0 := by omega
    have h1 : skPlace 0 0 0 (cupThick 0) = (1 : SkMat 0 0) := by
      rw [cupThick_zero]; exact skPlace_one 0 0 0 le_rfl
    have h2 : skPlace 0 0 0 (capThick 0) = (1 : SkMat 0 0) := by
      rw [capThick_zero]; exact skPlace_one 0 0 0 le_rfl
    rw [h1, h2, Matrix.mul_one]
  | succ c ih =>
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨3 * c + 1, by omega⟩
    have hcomm := skPlace_mul_skPlace_comm (c + 1 + 2) (M + 2) (c + 1) M (0 + 1) (0 + 1)
      (cupThick c) skCap (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [show 0 + 1 + 2 * c - 0 = c + 1 + c from by omega] at hcomm
    have hih := congrArg (skPlace (c + 1) (c + 1) 1) (ih (3 * c) rfl)
    rw [skPlace_mul (c + 1) M (c + 1) 1 _ _ (by omega) (by omega) (by omega),
      skPlace_skPlace (c + 1) M 1 0 (cupThick c) (by omega) (by omega) (by omega) (by omega),
      skPlace_skPlace M (c + 1) 1 c (capThick c) (by omega) (by omega) (by omega) (by omega),
      skPlace_one (c + 1) 1 c (by omega), Nat.add_zero, Nat.add_comm 1 c] at hih
    rw [skPlace_cupThick_succ (c + 1) (M + 2) 0 c (by omega) (by omega),
      skPlace_capThick_succ_inner c M (c + 1) (c + 1) (by omega) (by omega),
      Matrix.mul_assoc, ← Matrix.mul_assoc (skPlace (c + 1 + 2) (M + 2) (0 + 1) (cupThick c)),
      capAt, hcomm, Matrix.mul_assoc, Nat.zero_add, hih, Matrix.mul_one]
    exact cupAt_mul_capAt_succ (c + 1) 0 (by omega)

/-- Thick zig-zag: a bundle capped with the left bundle of a thick cup created on its right. -/
theorem cupThick_mul_capThick_right (c : ℕ) :
    skPlace c (3 * c) c (cupThick c) * skPlace (3 * c) c 0 (capThick c) = 1 :=
  cupThick_mul_capThick_right_thickCup c (3 * c) rfl

/-- Thick zig-zag: a bundle capped with the right bundle of a thick cup created on its left. -/
theorem cupThick_mul_capThick_left (c : ℕ) :
    skPlace c (3 * c) 0 (cupThick c) * skPlace (3 * c) c c (capThick c) = 1 :=
  cupThick_mul_capThick_left_thickCup c (3 * c) rfl

end AJConjecture
