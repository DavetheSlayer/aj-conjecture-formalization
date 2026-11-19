import Mathlib
import AJConjecture.SkeinPlaceAppend

/-!
# The interchange law (far commutation)

Operators placed on disjoint windows commute; when the first one changes the number of
strands, the position of the second one is shifted: for `A` from `k` to `l` factors at the
position `i` and `B` from `k'` to `l'` factors at a position `j ≥ i + k`,
`(1 ⊗ A ⊗ 1)(1 ⊗ B ⊗ 1) = (1 ⊗ B ⊗ 1)(1 ⊗ A ⊗ 1)` with `B` at the position `j + l - k` on the
left-hand side. Proof: entrywise; both sides are the product of an entry of `A` and an entry of
`B` when the states agree outside the two windows.
-/

namespace AJConjecture

/-- Two concatenated states are equal exactly when their parts are equal. -/
theorem fin_append_inj {m n : ℕ} (a a' : Fin m → Bool) (b b' : Fin n → Bool) :
    Fin.append a b = Fin.append a' b' ↔ a = a' ∧ b = b' := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h₁, h₂⟩ ↦ by rw [h₁, h₂]⟩
  · funext x
    simpa only [Fin.append_left] using congrFun h (Fin.castAdd n x)
  · funext x
    simpa only [Fin.append_right] using congrFun h (Fin.natAdd m x)

/-- Every state of `m + n` factors is a concatenation of two states. -/
private theorem exists_append_placeComm {m n : ℕ} (a : Fin (m + n) → Bool) :
    ∃ (a₁ : Fin m → Bool) (a₂ : Fin n → Bool), a = Fin.append a₁ a₂ :=
  ⟨_, _, Fin.append_castAdd_natAdd.symm⟩

/-- Every state of `i + k + u + p + s` factors is a concatenation of five states. -/
private theorem exists_append₅_placeComm (i k u p s : ℕ) (a : Fin (i + k + u + p + s) → Bool) :
    ∃ (a₁ : Fin i → Bool) (a₂ : Fin k → Bool) (a₃ : Fin u → Bool) (a₄ : Fin p → Bool)
      (a₅ : Fin s → Bool),
      a = Fin.append (Fin.append (Fin.append (Fin.append a₁ a₂) a₃) a₄) a₅ := by
  obtain ⟨x, a₅, rfl⟩ := exists_append_placeComm a
  obtain ⟨y, a₄, rfl⟩ := exists_append_placeComm x
  obtain ⟨z, a₃, rfl⟩ := exists_append_placeComm y
  obtain ⟨a₁, a₂, rfl⟩ := exists_append_placeComm z
  exact ⟨a₁, a₂, a₃, a₄, a₅, rfl⟩

/-- The entries of a placement do not depend on how the ambient sizes are written. -/
private theorem skPlace_comp_cast_placeComm {n n' m m' : ℕ} (i : ℕ) {k l : ℕ} (A : SkMat k l)
    (hn : n = m) (hn' : n' = m') (a : Fin m → Bool) (b : Fin m' → Bool) :
    skPlace n n' i A (a ∘ Fin.cast hn) (b ∘ Fin.cast hn') = skPlace m m' i A a b := by
  subst hn hn'
  rfl

/-- The entries of a placement on the second of five blocks. -/
private theorem skPlace_append₅_left_placeComm (i u p s : ℕ) {k l : ℕ} (A : SkMat k l)
    (a₁ b₁ : Fin i → Bool) (a₂ : Fin k → Bool) (b₂ : Fin l → Bool) (a₃ b₃ : Fin u → Bool)
    (a₄ b₄ : Fin p → Bool) (a₅ b₅ : Fin s → Bool) :
    skPlace (i + k + u + p + s) (i + l + u + p + s) i A
        (Fin.append (Fin.append (Fin.append (Fin.append a₁ a₂) a₃) a₄) a₅)
        (Fin.append (Fin.append (Fin.append (Fin.append b₁ b₂) b₃) b₄) b₅) =
      if a₁ = b₁ ∧ a₃ = b₃ ∧ a₄ = b₄ ∧ a₅ = b₅ then A a₂ b₂ else 0 := by
  rw [Fin.append_assoc (Fin.append (Fin.append a₁ a₂) a₃) a₄ a₅,
    Fin.append_assoc (Fin.append a₁ a₂) a₃ (Fin.append a₄ a₅),
    Fin.append_assoc (Fin.append (Fin.append b₁ b₂) b₃) b₄ b₅,
    Fin.append_assoc (Fin.append b₁ b₂) b₃ (Fin.append b₄ b₅),
    skPlace_comp_cast_placeComm, skPlace_comp_cast_placeComm, skPlace_append_apply]
  simp only [fin_append_inj]

/-- The entries of a placement on the fourth of five blocks. -/
private theorem skPlace_append₅_right_placeComm (i p u s : ℕ) {k l : ℕ} (B : SkMat k l)
    (a₁ b₁ : Fin i → Bool) (a₂ b₂ : Fin p → Bool) (a₃ b₃ : Fin u → Bool)
    (a₄ : Fin k → Bool) (b₄ : Fin l → Bool) (a₅ b₅ : Fin s → Bool) :
    skPlace (i + p + u + k + s) (i + p + u + l + s) (i + p + u) B
        (Fin.append (Fin.append (Fin.append (Fin.append a₁ a₂) a₃) a₄) a₅)
        (Fin.append (Fin.append (Fin.append (Fin.append b₁ b₂) b₃) b₄) b₅) =
      if a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ ∧ a₅ = b₅ then B a₄ b₄ else 0 := by
  rw [skPlace_append_apply]
  simp only [fin_append_inj, and_assoc]

/-- The interchange law for two placements on disjoint windows. -/
theorem skPlace_mul_skPlace_comm (n n₁ n₂ n' i j : ℕ) {k l k' l' : ℕ} (A : SkMat k l)
    (B : SkMat k' l') (hij : i + k ≤ j) (hj : j + k' ≤ n) (h₁ : n + l = n₁ + k)
    (h₂ : n + l' = n₂ + k') (h' : n₁ + l' = n' + k') :
    skPlace n n₁ i A * skPlace n₁ n' (j + l - k) B = skPlace n n₂ j B * skPlace n₂ n' i A := by
  obtain ⟨u, rfl⟩ : ∃ u, j = i + k + u := ⟨j - (i + k), by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, n = i + k + u + k' + s := ⟨n - (i + k + u + k'), by omega⟩
  obtain rfl : n₁ = i + l + u + k' + s := by omega
  obtain rfl : n₂ = i + k + u + l' + s := by omega
  obtain rfl : n' = i + l + u + l' + s := by omega
  have e : i + k + u + l - k = i + l + u := by omega
  rw [e]
  ext a b
  obtain ⟨a₁, a₂, a₃, a₄, a₅, rfl⟩ := exists_append₅_placeComm i k u k' s a
  obtain ⟨b₁, b₂, b₃, b₄, b₅, rfl⟩ := exists_append₅_placeComm i l u l' s b
  rw [Matrix.mul_apply, Matrix.mul_apply,
    Fintype.sum_eq_single (Fin.append (Fin.append (Fin.append (Fin.append a₁ b₂) a₃) a₄) a₅),
    Fintype.sum_eq_single (Fin.append (Fin.append (Fin.append (Fin.append a₁ a₂) a₃) b₄) a₅)]
  · rw [skPlace_append₅_left_placeComm, skPlace_append₅_right_placeComm,
      skPlace_append₅_left_placeComm, skPlace_append₅_right_placeComm]
    by_cases g₁ : a₁ = b₁ <;> by_cases g₃ : a₃ = b₃ <;> by_cases g₅ : a₅ = b₅ <;>
      simp [g₁, g₃, g₅, mul_comm]
  · intro c hc
    obtain ⟨c₁, c₂, c₃, c₄, c₅, rfl⟩ := exists_append₅_placeComm i k u l' s c
    rw [skPlace_append₅_left_placeComm, skPlace_append₅_right_placeComm]
    simp only [fin_append_inj, ne_eq] at hc
    by_contra hne
    obtain ⟨g, g'⟩ := mul_ne_zero_iff.mp hne
    have gP := (ite_ne_right_iff.mp g).1
    have gQ := (ite_ne_right_iff.mp g').1
    exact hc ⟨⟨⟨⟨gP.1.symm, gP.2.1.symm⟩, gP.2.2.1.symm⟩, gQ.2.2.1⟩, gP.2.2.2.symm⟩
  · intro c hc
    obtain ⟨c₁, c₂, c₃, c₄, c₅, rfl⟩ := exists_append₅_placeComm i l u k' s c
    rw [skPlace_append₅_left_placeComm, skPlace_append₅_right_placeComm]
    simp only [fin_append_inj, ne_eq] at hc
    by_contra hne
    obtain ⟨g, g'⟩ := mul_ne_zero_iff.mp hne
    have gP := (ite_ne_right_iff.mp g).1
    have gQ := (ite_ne_right_iff.mp g').1
    exact hc ⟨⟨⟨⟨gP.1.symm, gQ.2.1⟩, gP.2.1.symm⟩, gP.2.2.1.symm⟩, gP.2.2.2.symm⟩

end AJConjecture
