import Mathlib

/-!
# Torsion and centre of the free product `C_r * C_s`

Normal forms in the free product of two finite cyclic groups: every element of finite order is
conjugate into a factor, so its order divides `r` or `s`; and for `r, s ≥ 2` the centre is
trivial. Route: transfer to `Monoid.CoprodI` over `Bool` (reduced words `Monoid.CoprodI.Word`),
cyclic reduction (an element is conjugate to a factor element or to a cyclically reduced
alternating word of even length ≥ 2, whose powers are again reduced, hence of infinite order), and
for the centre compare the first letters of `a · w` and `w · a`.
-/

namespace AJConjecture

namespace CoprodINormalForm

open Monoid CoprodI

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-- A list of letters is reduced: no letter is `1` and adjacent letters lie in different
factors. -/
def IsReducedList (L : List (Σ i, G i)) : Prop :=
  (∀ l ∈ L, l.2 ≠ 1) ∧ L.IsChain fun l l' ↦ l.1 ≠ l'.1

/-- The product in the free product of a list of letters. -/
def listProd (L : List (Σ i, G i)) : CoprodI G :=
  (L.map fun l ↦ of l.2).prod

/-- The product of the empty list is `1`. -/
theorem listProd_nil : listProd ([] : List (Σ i, G i)) = 1 := rfl

/-- The product of `l :: L` is the letter `l` times the product of `L`. -/
theorem listProd_cons (l : Σ i, G i) (L : List (Σ i, G i)) :
    listProd (l :: L) = of l.2 * listProd L := by
  simp [listProd]

/-- The product of a concatenation is the product of the products. -/
theorem listProd_append (L L' : List (Σ i, G i)) :
    listProd (L ++ L') = listProd L * listProd L' := by
  simp [listProd]

/-- The product of a one-letter list is that letter. -/
theorem listProd_singleton (l : Σ i, G i) : listProd [l] = of l.2 := by
  simp [listProd]

/-- The product of `n` copies of `L` is the `n`-th power of the product of `L`. -/
theorem listProd_flatten_replicate (L : List (Σ i, G i)) (n : ℕ) :
    listProd (List.replicate n L).flatten = listProd L ^ n := by
  induction n with
  | zero => simp [listProd_nil]
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, listProd_append, ih, pow_succ']

/-- A concatenation is reduced iff both parts are and the junction letters lie in different
factors. -/
theorem isReducedList_append_iff {L L' : List (Σ i, G i)} :
    IsReducedList (L ++ L') ↔ IsReducedList L ∧ IsReducedList L' ∧
      ∀ x ∈ L.getLast?, ∀ y ∈ L'.head?, x.1 ≠ y.1 := by
  simp only [IsReducedList, List.forall_mem_append, List.isChain_append]
  tauto

/-- The empty list is reduced. -/
theorem isReducedList_nil : IsReducedList ([] : List (Σ i, G i)) := by
  simp [IsReducedList]

/-- A one-letter list is reduced iff its letter is not `1`. -/
theorem isReducedList_singleton {l : Σ i, G i} : IsReducedList [l] ↔ l.2 ≠ 1 := by
  simp [IsReducedList]

/-- `l :: L` is reduced iff `l ≠ 1`, `l` and the head of `L` lie in different factors, and
`L` is reduced. -/
theorem isReducedList_cons_iff {l : Σ i, G i} {L : List (Σ i, G i)} :
    IsReducedList (l :: L) ↔ l.2 ≠ 1 ∧ (∀ y ∈ L.head?, l.1 ≠ y.1) ∧ IsReducedList L := by
  rw [← List.singleton_append, isReducedList_append_iff, isReducedList_singleton]
  simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq, forall_eq', ne_eq]
  tauto

omit [∀ i, Group (G i)] in
/-- Every list of length at least two has a first and a last letter. -/
theorem list_cases_first_last (L : List (Σ i, G i)) :
    L = [] ∨ (∃ x, L = [x]) ∨ ∃ x L' z, L = x :: (L' ++ [z]) := by
  rcases L with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨x, rfl⟩)
  · exact Or.inr (Or.inr ⟨x, _, _, congrArg (x :: ·)
      (List.dropLast_append_getLast (List.cons_ne_nil y rest)).symm⟩)

/-- A cyclically reduced list (first and last letters in different factors) stays reduced when
repeated. -/
theorem isReducedList_flatten_replicate {L : List (Σ i, G i)} (hL : IsReducedList L)
    (hne : L ≠ []) (hc : ∀ x ∈ L.getLast?, ∀ y ∈ L.head?, x.1 ≠ y.1) (n : ℕ) :
    IsReducedList (List.replicate (n + 1) L).flatten := by
  induction n with
  | zero => simpa using hL
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, isReducedList_append_iff]
    refine ⟨hL, ih, ?_⟩
    rw [List.replicate_succ, List.flatten_cons, List.head?_append_of_ne_nil _ hne]
    exact hc

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- Uniqueness of normal forms: reduced lists with the same product are equal. -/
theorem eq_of_listProd_eq {L L' : List (Σ i, G i)} (hL : IsReducedList L)
    (hL' : IsReducedList L') (h : listProd L = listProd L') : L = L' := by
  have := (Word.equiv (M := G)).symm.injective (a₁ := ⟨L, hL.1, hL.2⟩)
    (a₂ := ⟨L', hL'.1, hL'.2⟩) h
  exact congrArg Word.toList this

/-- Existence of normal forms: every element is the product of a reduced list. -/
theorem exists_reduced (g : CoprodI G) :
    ∃ L : List (Σ i, G i), IsReducedList L ∧ listProd L = g :=
  ⟨(Word.equiv g).toList, ⟨(Word.equiv g).ne_one, (Word.equiv g).chain_ne⟩,
    (Word.equiv (M := G)).symm_apply_apply g⟩

/-- A nonempty reduced list has product different from `1`. -/
theorem listProd_ne_one {L : List (Σ i, G i)} (hL : IsReducedList L) (hne : L ≠ []) :
    listProd L ≠ 1 := fun h ↦ hne (eq_of_listProd_eq hL isReducedList_nil h)

/-- A cyclically reduced nonempty word has infinite order. -/
theorem not_isOfFinOrder_of_ne {L : List (Σ i, G i)} (hL : IsReducedList L)
    (hne : L ≠ []) (hc : ∀ x ∈ L.getLast?, ∀ y ∈ L.head?, x.1 ≠ y.1) :
    ¬ IsOfFinOrder (listProd L) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, h⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [zero_add, ← listProd_flatten_replicate] at h
  refine listProd_ne_one (isReducedList_flatten_replicate hL hne hc k) ?_ h
  simp [hne]

/-- Conjugate elements of a group have the same order. -/
theorem orderOf_eq_of_isConj {H : Type*} [Group H] {a b : H} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a
  simpa using this.symm

/-- An element of finite order of a free product of groups, given by a reduced list, is conjugate
to an element of a factor. -/
theorem exists_isConj_of_isOfFinOrder [Nonempty ι] (n : ℕ) :
    ∀ L : List (Σ i, G i), L.length = n → IsReducedList L → IsOfFinOrder (listProd L) →
      ∃ (i : ι) (m : G i), IsConj (listProd L) (of m) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hlen hL hg
  rcases list_cases_first_last L with rfl | ⟨x, rfl⟩ | ⟨⟨i, a⟩, L', ⟨k, b⟩, rfl⟩
  · exact ⟨Classical.arbitrary ι, 1, by simp [listProd_nil]⟩
  · exact ⟨x.1, x.2, by rw [listProd_singleton]⟩
  by_cases hik : i = k
  swap
  · refine absurd hg (not_isOfFinOrder_of_ne hL (List.cons_ne_nil _ _) ?_)
    simp only [List.getLast?_cons, List.getLast?_append,
      Option.some_or, Option.getD_some, List.head?_cons, Option.mem_def, Option.some.injEq]
    rintro _ rfl _ rfl
    exact Ne.symm hik
  subst hik
  obtain ⟨-, -, hL'⟩ := isReducedList_cons_iff.1 hL
  obtain ⟨hL'', -, hlast⟩ := isReducedList_append_iff.1 hL'
  have hconj : IsConj (listProd (⟨i, a⟩ :: (L' ++ [⟨i, b⟩]))) (listProd L' * of (b * a)) := by
    refine isConj_iff.2 ⟨of a⁻¹, ?_⟩
    simp only [listProd_cons, listProd_append, listProd_nil, mul_one, map_inv, inv_inv, map_mul]
    group
  have hlen' : L'.length < n := by subst hlen; simp
  by_cases hba : b * a = 1
  · rw [hba, map_one, mul_one] at hconj
    obtain ⟨j, m, hm⟩ := ih _ hlen' L' rfl hL'' (hconj.isOfFinOrder hg)
    exact ⟨j, m, hconj.trans hm⟩
  · have hred : IsReducedList (L' ++ [⟨i, b * a⟩]) := by
      refine isReducedList_append_iff.2 ⟨hL'', isReducedList_singleton.2 hba, ?_⟩
      simpa using hlast
    rw [← listProd_singleton (⟨i, b * a⟩ : Σ i, G i), ← listProd_append] at hconj
    obtain ⟨j, m, hm⟩ := ih (L'.length + 1) (by subst hlen; simp) _ (by simp) hred
      (hconj.isOfFinOrder hg)
    exact ⟨j, m, hconj.trans hm⟩

/-- A nonempty reduced word whose first and last letters lie in the same factor does not commute
with all elements of the factors (when every factor has a nontrivial factor beside it). -/
theorem false_of_head_eq_last (hnt : ∀ i, ∃ j, j ≠ i ∧ ∃ m : G j, m ≠ 1)
    {x : Σ i, G i} {R : List (Σ i, G i)} (hg : ∀ i (m : G i), of m * listProd (x :: R) =
      listProd (x :: R) * of m)
    (hL : IsReducedList (x :: R)) (hlast : ∀ z ∈ (x :: R).getLast?, z.1 = x.1) : False := by
  obtain ⟨j, hj, m, hm⟩ := hnt x.1
  have h1 : IsReducedList (⟨j, m⟩ :: x :: R) :=
    isReducedList_cons_iff.2 ⟨hm, by simpa using hj, hL⟩
  have h2 : IsReducedList ((x :: R) ++ [⟨j, m⟩]) := by
    refine isReducedList_append_iff.2 ⟨hL, isReducedList_singleton.2 hm, ?_⟩
    intro y hy _ hj'
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hj'
    subst hj'
    rw [hlast y hy]
    exact hj.symm
  have heq := eq_of_listProd_eq h1 h2 (by
    rw [listProd_cons, listProd_append, listProd_singleton (⟨j, m⟩ : Σ i, G i)]
    exact hg j m)
  rw [List.cons_append] at heq
  exact hj (congrArg Sigma.fst (List.head_eq_of_cons_eq heq))

/-- In a free product in which every factor has a nontrivial other factor, an element commuting
with all elements of all factors is trivial. -/
theorem eq_one_of_forall_commute (hnt : ∀ i, ∃ j, j ≠ i ∧ ∃ m : G j, m ≠ 1) (g : CoprodI G)
    (hg : ∀ i (m : G i), of m * g = g * of m) : g = 1 := by
  obtain ⟨L, hL, rfl⟩ := exists_reduced g
  rcases list_cases_first_last L with rfl | ⟨x, rfl⟩ | ⟨x, L', z, rfl⟩
  · rfl
  · exact (false_of_head_eq_last hnt hg hL (by simp)).elim
  by_cases hxz : z.1 = x.1
  · refine (false_of_head_eq_last hnt hg hL ?_).elim
    rw [← List.cons_append, List.getLast?_concat]
    simpa using hxz
  exfalso
  have hz : z.2 ≠ 1 := hL.1 z (by simp)
  have h1 : IsReducedList (⟨z.1, z.2⁻¹⟩ :: x :: (L' ++ [z])) :=
    isReducedList_cons_iff.2 ⟨inv_ne_one.2 hz, by simpa using hxz, hL⟩
  have h2 : IsReducedList (x :: L') := by
    rw [← List.cons_append] at hL
    exact (isReducedList_append_iff.1 hL).1
  have heq := eq_of_listProd_eq h1 h2 (by
    rw [listProd_cons, hg, ← List.cons_append, listProd_append, listProd_singleton]
    simp)
  have hzx := List.head_eq_of_cons_eq heq
  exact hxz (by rw [← hzx])

section Transfer

universe u

variable {M N : Type u} [Group M] [Group N]

/-- The group structure on the factors `cond b M N` of the indexed coproduct over `Bool`. -/
scoped instance instGroupCondBool : ∀ b : Bool, Group (cond b M N)
  | true => ‹Group M›
  | false => ‹Group N›

/-- The canonical map from the binary coproduct `M ∗ N` to the indexed coproduct over `Bool`. -/
def coprodToCoprodI : Monoid.Coprod M N →* CoprodI (fun b : Bool ↦ cond b M N) :=
  Monoid.Coprod.lift (of (M := fun b : Bool ↦ cond b M N) (i := true))
    (of (M := fun b : Bool ↦ cond b M N) (i := false))

/-- The canonical map from the indexed coproduct over `Bool` back to `M ∗ N`. -/
def coprodIToCoprod : CoprodI (fun b : Bool ↦ cond b M N) →* Monoid.Coprod M N :=
  CoprodI.lift fun b ↦ Bool.rec (motive := fun b ↦ cond b M N →* Monoid.Coprod M N)
    Monoid.Coprod.inr Monoid.Coprod.inl b

/-- `coprodToCoprodI` sends `inl x` to the letter `x` of the factor `true`. -/
theorem coprodToCoprodI_inl (x : M) :
    coprodToCoprodI (Monoid.Coprod.inl x : Monoid.Coprod M N) =
      of (M := fun b : Bool ↦ cond b M N) (i := true) x :=
  Monoid.Coprod.lift_apply_inl _ _ x

/-- `coprodToCoprodI` sends `inr x` to the letter `x` of the factor `false`. -/
theorem coprodToCoprodI_inr (x : N) :
    coprodToCoprodI (Monoid.Coprod.inr x : Monoid.Coprod M N) =
      of (M := fun b : Bool ↦ cond b M N) (i := false) x :=
  Monoid.Coprod.lift_apply_inr _ _ x

/-- `coprodIToCoprod` is a left inverse of `coprodToCoprodI`. -/
theorem coprodIToCoprod_comp_coprodToCoprodI :
    (coprodIToCoprod (M := M) (N := N)).comp coprodToCoprodI = MonoidHom.id _ := by
  apply Monoid.Coprod.hom_ext
  · ext x
    simp only [MonoidHom.comp_apply, coprodToCoprodI_inl, MonoidHom.id_apply, coprodIToCoprod,
      CoprodI.lift_of]
  · ext x
    simp only [MonoidHom.comp_apply, coprodToCoprodI_inr, MonoidHom.id_apply, coprodIToCoprod,
      CoprodI.lift_of]

/-- The canonical map `M ∗ N → CoprodI (cond · M N)` is injective. -/
theorem coprodToCoprodI_injective :
    Function.Injective (coprodToCoprodI (M := M) (N := N)) :=
  Function.LeftInverse.injective (g := coprodIToCoprod) fun x ↦
    DFunLike.congr_fun coprodIToCoprod_comp_coprodToCoprodI x

end Transfer

end CoprodINormalForm

open CoprodINormalForm in
/-- In `C_r * C_s`, an element of finite order has order dividing `r` or `s`. -/
theorem orderOf_dvd_of_isOfFinOrder_coprodCyclic {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {g : Monoid.Coprod (Multiplicative (ZMod r)) (Multiplicative (ZMod s))}
    (hg : IsOfFinOrder g) : orderOf g ∣ r ∨ orderOf g ∣ s := by
  classical
  have : NeZero r := ⟨hr.ne'⟩
  have : NeZero s := ⟨hs.ne'⟩
  have hφ := coprodToCoprodI_injective (M := Multiplicative (ZMod r))
    (N := Multiplicative (ZMod s))
  rw [← orderOf_injective _ hφ g]
  rw [← hφ.isOfFinOrder_iff] at hg
  obtain ⟨L, hL, hLg⟩ := exists_reduced (coprodToCoprodI g)
  rw [← hLg] at hg ⊢
  obtain ⟨i, m, hm⟩ := exists_isConj_of_isOfFinOrder _ L rfl hL hg
  have hof := orderOf_injective (Monoid.CoprodI.of (M := fun b : Bool ↦
    cond b (Multiplicative (ZMod r)) (Multiplicative (ZMod s))) (i := i))
    (Monoid.CoprodI.of_injective i) m
  have hord : orderOf (listProd L) = orderOf m := (orderOf_eq_of_isConj hm).trans hof
  rw [hord]
  cases i
  · exact Or.inr ((orderOf_dvd_card (G := Multiplicative (ZMod s)) (x := m)).trans (by simp))
  · exact Or.inl ((orderOf_dvd_card (G := Multiplicative (ZMod r)) (x := m)).trans (by simp))

open CoprodINormalForm in
/-- For `r, s ≥ 2` the centre of `C_r * C_s` is trivial. -/
theorem center_coprodCyclic_eq_bot {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) :
    Subgroup.center (Monoid.Coprod (Multiplicative (ZMod r)) (Multiplicative (ZMod s))) = ⊥ := by
  classical
  have : Fact (1 < r) := ⟨hr⟩
  have : Fact (1 < s) := ⟨hs⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦ ?_
  rw [Subgroup.mem_center_iff] at hg
  apply coprodToCoprodI_injective
  rw [map_one]
  refine eq_one_of_forall_commute (fun i ↦ ?_) _ fun i m ↦ ?_
  · cases i
    · exact ⟨true, by decide, Multiplicative.ofAdd (1 : ZMod r),
        (by simp : Multiplicative.ofAdd (1 : ZMod r) ≠ 1)⟩
    · exact ⟨false, by decide, Multiplicative.ofAdd (1 : ZMod s),
        (by simp : Multiplicative.ofAdd (1 : ZMod s) ≠ 1)⟩
  · cases i
    · have h := congrArg coprodToCoprodI (hg (Monoid.Coprod.inr m))
      rwa [map_mul, map_mul, coprodToCoprodI_inr] at h
    · have h := congrArg coprodToCoprodI (hg (Monoid.Coprod.inl m))
      rwa [map_mul, map_mul, coprodToCoprodI_inl] at h

end AJConjecture
