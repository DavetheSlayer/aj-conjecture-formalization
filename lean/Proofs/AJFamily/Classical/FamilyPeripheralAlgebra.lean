import Mathlib
import AJFamily.Classical.FamilyPeripheralCompanion

/-!
# The satellite relations from the block relations

Pure group theory. From the relations that the run of `whiteheadTorusWord k` imposes on the
block loops `L r` of `famBlocks k`, the meridian `a` and the edge meridians `α`, `β` of the two
clasp levels, `isSatelliteData_of_famRelations` derives `IsSatelliteData` with companion
generators `c = L (4k+1)`, `d = L (2k)` and second clasp arc `a₁ = λ⁻¹ a λ`,
`λ = compLong k c d`. The steps are the loop values (`fam_loopValues`), the orbit loop of the
strand `0` (`fam_orbitLoop_values`) and the clasp identity `d = α β⁻¹ α⁻¹ β` (`fam_clasp`).
-/

namespace AJConjecture

variable {G : Type*} [Group G]

/-- The orbit of the strand `0` under the strand permutation of `whiteheadTorusWord k`:
`0; 4k+1, 4k-1, …, 2k+1; 1, …, 2k-1; 4k, 4k-2, …, 2k; 4k+2`. -/
def famCycle (k t : ℕ) : ℕ :=
  if t = 0 then 0
  else if t ≤ k + 1 then 4 * k + 3 - 2 * t
  else if t ≤ 3 * k then t - k - 1
  else if t ≤ 4 * k + 1 then 10 * k + 2 - 2 * t
  else 4 * k + 2

/-- The loop collected by the strand at top position `t` of the family word, in terms of the
block loops `L r`. -/
def famStrandLoop (k : ℕ) (L : ℕ → G) (t : ℕ) : G :=
  if t = 0 then ((List.range k).reverse.map fun r ↦ L (2 * k + 2 + 2 * r)).prod
  else if t ≤ 2 * k - 1 then L (4 * k + 1)
  else if t = 2 * k then L (2 * k + 1)
  else if t = 2 * k + 1 then L (4 * k + 2) * L (4 * k + 1)
  else if t ≤ 4 * k then L (4 * k + 2) * L (2 * k + 2 + (4 * k - t)) * L (2 * k - 1)
  else if t = 4 * k + 1 then L (4 * k + 3) * L (2 * k) * L (2 * k - 1)
  else L (4 * k + 2) * L (4 * k + 1) *
    ((List.range (k - 1)).reverse.map fun r ↦ L (2 * k + 3 + 2 * r)).prod *
    L (2 * k) * L (2 * k - 1) * ((List.range (2 * k - 1)).reverse.map L).prod

/-- The product of the strand loops along the orbit of `0`. -/
def famOrbitLoop (k : ℕ) (L : ℕ → G) : G :=
  ((List.range (4 * k + 3)).map fun j ↦ famStrandLoop k L (famCycle k j)).prod

/-- Splitting a product over `List.range (n + m)`. -/
private theorem prod_range_add_map (f : ℕ → G) (n m : ℕ) :
    ((List.range (n + m)).map f).prod =
      ((List.range n).map f).prod * ((List.range m).map fun j ↦ f (n + j)).prod := by
  rw [List.range_add, List.map_append, List.prod_append, List.map_map]
  rfl

/-- Products over `List.range n` of functions agreeing below `n`. -/
private theorem prod_map_range_congr {f g : ℕ → G} {n : ℕ} (h : ∀ j < n, f j = g j) :
    ((List.range n).map f).prod = ((List.range n).map g).prod := by
  rw [List.map_congr_left (fun j hj ↦ h j (List.mem_range.1 hj))]

/-- Products over `(List.range n).reverse` of functions agreeing below `n`. -/
private theorem prod_map_reverse_range_congr {f g : ℕ → G} {n : ℕ} (h : ∀ j < n, f j = g j) :
    ((List.range n).reverse.map f).prod = ((List.range n).reverse.map g).prod := by
  rw [List.map_congr_left (fun j hj ↦ h j (List.mem_range.1 (List.mem_reverse.1 hj)))]

theorem famOrbitLoop_eq (k : ℕ) (hk : 1 ≤ k) (L : ℕ → G) :
    famOrbitLoop k L =
      famStrandLoop k L 0 * famStrandLoop k L (4 * k + 1) *
        ((List.range (k - 1)).map fun r ↦ famStrandLoop k L (4 * k - 1 - 2 * r)).prod *
        famStrandLoop k L (2 * k + 1) * L (4 * k + 1) ^ (2 * k - 1) *
        ((List.range k).map fun r ↦ famStrandLoop k L (4 * k - 2 * r)).prod *
        famStrandLoop k L (2 * k) * famStrandLoop k L (4 * k + 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [famOrbitLoop,
    show 4 * (m + 1) + 3 = 1 + 1 + m + 1 + (2 * m + 1) + (m + 1) + 1 + 1 by ring]
  rw [prod_range_add_map _ (1 + 1 + m + 1 + (2 * m + 1) + (m + 1) + 1) 1,
    prod_range_add_map _ (1 + 1 + m + 1 + (2 * m + 1) + (m + 1)) 1,
    prod_range_add_map _ (1 + 1 + m + 1 + (2 * m + 1)) (m + 1),
    prod_range_add_map _ (1 + 1 + m + 1) (2 * m + 1), prod_range_add_map _ (1 + 1 + m) 1,
    prod_range_add_map _ (1 + 1) m, prod_range_add_map _ 1 1]
  simp only [List.range_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, Nat.add_sub_cancel]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · rfl
  · rw [show famCycle (m + 1) (1 + 0) = 4 * (m + 1) + 1 by unfold famCycle; split_ifs <;> omega]
  · refine prod_map_range_congr fun j hj ↦ ?_
    rw [show famCycle (m + 1) (1 + 1 + j) = 4 * (m + 1) - 1 - 2 * j by
      unfold famCycle; split_ifs <;> omega]
  · rw [show famCycle (m + 1) (1 + 1 + m + 0) = 2 * (m + 1) + 1 by
      unfold famCycle; split_ifs <;> omega]
  · have hconst : ∀ j < 2 * m + 1,
        famStrandLoop (m + 1) L (famCycle (m + 1) (1 + 1 + m + 1 + j)) = L (4 * (m + 1) + 1) := by
      intro j hj
      rw [show famCycle (m + 1) (1 + 1 + m + 1 + j) = j + 1 by
        unfold famCycle; split_ifs <;> omega]
      unfold famStrandLoop
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    rw [prod_map_range_congr (g := fun _ ↦ L (4 * (m + 1) + 1)) hconst, List.map_const',
      List.prod_replicate, List.length_range, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
  · refine prod_map_range_congr fun j hj ↦ ?_
    rw [show famCycle (m + 1) (1 + 1 + m + 1 + (2 * m + 1) + j) = 4 * (m + 1) - 2 * j by
      unfold famCycle; split_ifs <;> omega]
  · rw [show famCycle (m + 1) (1 + 1 + m + 1 + (2 * m + 1) + (m + 1) + 0) = 2 * (m + 1) by
      unfold famCycle; split_ifs <;> omega]
  · rw [show famCycle (m + 1) (1 + 1 + m + 1 + (2 * m + 1) + (m + 1) + 1 + 0) = 4 * (m + 1) + 2 by
      unfold famCycle; split_ifs <;> omega]

theorem fam_clasp (k : ℕ) (L : ℕ → G) (α β : G)
    (hW6 : L (4 * k + 2) * L (2 * k) = 1)
    (hW7 : L (4 * k + 3) * L (2 * k + 1) = 1)
    (hH1 : L (2 * k + 1) = L (2 * k) * β⁻¹ * α)
    (hH2 : L (4 * k + 3) =
      L (4 * k + 2) * L (2 * k) * β⁻¹ * (L (2 * k + 1))⁻¹ * α * (L (2 * k + 1))⁻¹) :
    L (2 * k) = α * β⁻¹ * α⁻¹ * β := by
  rw [hH2, hW6, one_mul] at hW7
  generalize L (2 * k + 1) = h at hW7 hH1
  have hα : α = h * β := by
    calc α = h * β * (β⁻¹ * h⁻¹ * α * h⁻¹ * h) := by group
      _ = h * β := by rw [hW7, mul_one]
  subst hα
  calc L (2 * k) = (L (2 * k) * β⁻¹ * (h * β)) * β⁻¹ * h⁻¹ * β := by group
    _ = h * β * β⁻¹ * (h * β)⁻¹ * β := by rw [← hH1]; group

theorem fam_loopValues (k : ℕ) (hk : 1 ≤ k) (L : ℕ → G)
    (hW1 : ∀ n, 1 ≤ n → n ≤ 2 * k - 1 → L (4 * k + 1) * L (n - 1) = 1)
    (hW2 : L (4 * k + 1) * L (2 * k - 1) = 1)
    (hW3 : L (4 * k + 2) * L (4 * k + 1) * L (4 * k) * L (2 * k - 1) = 1)
    (hW4 : ∀ n, 2 * k + 2 ≤ n → n ≤ 4 * k - 1 →
      L (4 * k + 2) * L (2 * k + 2 + (4 * k - n)) * L (2 * k + 2 + (4 * k - 1 - n)) *
        L (2 * k - 1) = 1)
    (hW5 : L (4 * k + 2) * L (2 * k + 2) * L (2 * k) * L (2 * k - 1) = 1)
    (hW6 : L (4 * k + 2) * L (2 * k) = 1) :
    (∀ l, l ≤ 2 * k - 2 → L l = (L (4 * k + 1))⁻¹) ∧ L (2 * k - 1) = (L (4 * k + 1))⁻¹ ∧
      L (4 * k + 2) = (L (2 * k))⁻¹ ∧
      (∀ s, s ≤ 2 * k - 2 → L (2 * k + 2 + s) = famSigma (L (4 * k + 1)) (L (2 * k)) s) ∧
      (L (4 * k + 1) * L (2 * k)) ^ k * L (4 * k + 1) =
        L (2 * k) * (L (4 * k + 1) * L (2 * k)) ^ k := by
  have hcl : ∀ l, l ≤ 2 * k - 2 → L l = (L (4 * k + 1))⁻¹ := fun l hl ↦
    eq_inv_of_mul_eq_one_right (by simpa using hW1 (l + 1) (by omega) (by omega))
  have hf : L (4 * k + 2) = (L (2 * k))⁻¹ := eq_inv_of_mul_eq_one_left hW6
  have hB : L (2 * k - 1) = (L (4 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_right hW2
  have hσ : ∀ s, s ≤ 2 * k - 2 →
      L (2 * k + 2 + s) = famSigma (L (4 * k + 1)) (L (2 * k)) s := by
    refine famSigma_of_rec k _ _ (fun s ↦ L (2 * k + 2 + s)) ?_ fun s hs ↦ ?_
    · rw [hf] at hW5
      calc L (2 * k + 2 + 0) = L (2 * k) * ((L (2 * k))⁻¹ * L (2 * k + 2) * L (2 * k) *
            L (2 * k - 1)) * (L (2 * k - 1))⁻¹ * (L (2 * k))⁻¹ := by group
        _ = _ := by rw [hW5, hB]; group
    · have h4 := hW4 (4 * k - 1 - s) (by omega) (by omega)
      rw [show 4 * k - (4 * k - 1 - s) = s + 1 by omega,
        show 4 * k - 1 - (4 * k - 1 - s) = s by omega, hf] at h4
      calc L (2 * k + 2 + (s + 1)) * L (2 * k + 2 + s) = L (2 * k) * ((L (2 * k))⁻¹ *
            L (2 * k + 2 + (s + 1)) * L (2 * k + 2 + s) * L (2 * k - 1)) * (L (2 * k - 1))⁻¹ := by
            group
        _ = _ := by rw [h4, hB]; group
  refine ⟨hcl, hB, hf, hσ, ?_⟩
  refine torus_of_famSigma k hk _ _ ?_
  rw [← hσ _ le_rfl, show 2 * k + 2 + (2 * k - 2) = 4 * k by omega]
  rw [hf] at hW3
  calc L (4 * k) = (L (4 * k + 1))⁻¹ * L (2 * k) * ((L (2 * k))⁻¹ * L (4 * k + 1) * L (4 * k) *
        L (2 * k - 1)) * (L (2 * k - 1))⁻¹ := by group
    _ = _ := by rw [hW3, hB]; group

theorem fam_orbitLoop_values (k : ℕ) (hk : 1 ≤ k) (L : ℕ → G) (c d : G)
    (hc : L (4 * k + 1) = c) (hd : L (2 * k) = d)
    (hcl : ∀ l, l ≤ 2 * k - 2 → L l = c⁻¹) (hB : L (2 * k - 1) = c⁻¹)
    (hf : L (4 * k + 2) = d⁻¹) (hσ : ∀ s, s ≤ 2 * k - 2 → L (2 * k + 2 + s) = famSigma c d s)
    (hW7 : L (4 * k + 3) * L (2 * k + 1) = 1) :
    famStrandLoop k L 0 = famG0 k c d ∧ famStrandLoop k L (4 * k + 2) = famU k c d ∧
      famOrbitLoop k L =
        famG0 k c d * (L (2 * k + 1))⁻¹ * famMC k c d * L (2 * k + 1) * famU k c d := by
  have hS0 : famStrandLoop k L 0 = famG0 k c d := by
    rw [famStrandLoop, ite_eq_left rfl, ← evenDesc_famSigma k c d]
    exact prod_map_reverse_range_congr fun r hr ↦ hσ _ (by omega)
  have hS2 : famStrandLoop k L (4 * k + 2) = famU k c d := by
    have hodd := oddDesc_famSigma k hk c d
    rw [← prod_map_reverse_range_congr (f := fun r ↦ L (2 * k + 3 + 2 * r))
      fun r hr ↦ by rw [← hσ _ (by omega)]; ring_nf] at hodd
    have hcst : ((List.range (2 * k - 1)).reverse.map L).prod = (c⁻¹) ^ (2 * k - 1) := by
      rw [prod_map_reverse_range_congr (g := fun _ ↦ c⁻¹) fun r hr ↦ hcl r (by omega),
        List.map_const', List.prod_replicate, List.length_reverse, List.length_range]
    unfold famStrandLoop
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), hodd, hcst,
      hf, hc, hd, hB, famU]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 3 * (m + 1) - 1 = 3 * m + 2 by omega,
      Nat.add_sub_cancel]
    group
  refine ⟨hS0, hS2, ?_⟩
  have hh2 : L (4 * k + 3) = (L (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left hW7
  have hS1 : famStrandLoop k L (4 * k + 1) = (L (2 * k + 1))⁻¹ * d * c⁻¹ := by
    unfold famStrandLoop
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, hh2, hd, hB]
  have hSodd : ((List.range (k - 1)).map fun r ↦ famStrandLoop k L (4 * k - 1 - 2 * r)).prod =
      ((List.range (k - 1)).map fun r ↦ d⁻¹ * famSigma c d (2 * r + 1) * c⁻¹).prod := by
    refine prod_map_range_congr fun r hr ↦ ?_
    unfold famStrandLoop
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega), hf, hB,
      show 4 * k - (4 * k - 1 - 2 * r) = 2 * r + 1 by omega, hσ _ (by omega)]
  have hSmid : famStrandLoop k L (2 * k + 1) = d⁻¹ * c := by
    unfold famStrandLoop
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left rfl, hf, hc]
  have hSeven : ((List.range k).map fun r ↦ famStrandLoop k L (4 * k - 2 * r)).prod =
      ((List.range k).map fun r ↦ d⁻¹ * famSigma c d (2 * r) * c⁻¹).prod := by
    refine prod_map_range_congr fun r hr ↦ ?_
    unfold famStrandLoop
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_left (by omega), hf, hB,
      show 4 * k - (4 * k - 2 * r) = 2 * r by omega, hσ _ (by omega)]
  have hS2k : famStrandLoop k L (2 * k) = L (2 * k + 1) := by
    unfold famStrandLoop
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  rw [famOrbitLoop_eq k hk, hS0, hS1, hSodd, hSmid, hSeven, hS2k, hS2, hc,
    oddChain_famSigma k hk, evenChain_famSigma, famMC]
  group

theorem isSatelliteData_of_famRelations (k : ℕ) (hk : 1 ≤ k) (L : ℕ → G) (a α β l : G)
    (hW1 : ∀ n, 1 ≤ n → n ≤ 2 * k - 1 → L (4 * k + 1) * L (n - 1) = 1)
    (hW2 : L (4 * k + 1) * L (2 * k - 1) = 1)
    (hW3 : L (4 * k + 2) * L (4 * k + 1) * L (4 * k) * L (2 * k - 1) = 1)
    (hW4 : ∀ n, 2 * k + 2 ≤ n → n ≤ 4 * k - 1 →
      L (4 * k + 2) * L (2 * k + 2 + (4 * k - n)) * L (2 * k + 2 + (4 * k - 1 - n)) *
        L (2 * k - 1) = 1)
    (hW5 : L (4 * k + 2) * L (2 * k + 2) * L (2 * k) * L (2 * k - 1) = 1)
    (hW6 : L (4 * k + 2) * L (2 * k) = 1)
    (hW7 : L (4 * k + 3) * L (2 * k + 1) = 1)
    (hH1 : L (2 * k + 1) = L (2 * k) * β⁻¹ * α)
    (hH2 : L (4 * k + 3) =
      L (4 * k + 2) * L (2 * k) * β⁻¹ * (L (2 * k + 1))⁻¹ * α * (L (2 * k + 1))⁻¹)
    (hS0 : a = famStrandLoop k L 0 * β * (famStrandLoop k L 0)⁻¹)
    (hS2 : α = famStrandLoop k L (4 * k + 2) * a * (famStrandLoop k L (4 * k + 2))⁻¹)
    (hl : l = a ^ (4 * k : ℤ) * famOrbitLoop k L * a ^ (-(4 * k : ℤ)))
    (hcomm : famOrbitLoop k L * a = a * famOrbitLoop k L) :
    IsSatelliteData k a
      ((compLong k (L (4 * k + 1)) (L (2 * k)))⁻¹ * a * compLong k (L (4 * k + 1)) (L (2 * k)))
      (L (2 * k)) l := by
  obtain ⟨hcl, hB, hf, hσ, hT⟩ := fam_loopValues k hk L hW1 hW2 hW3 hW4 hW5 hW6
  obtain ⟨h0, h2, hO⟩ := fam_orbitLoop_values k hk L _ _ rfl rfl hcl hB hf hσ hW7
  have hd := fam_clasp k L α β hW6 hW7 hH1 hH2
  have hU := famU_conj k hk _ _ hT
  have hGU := famG0_mul_famU k hk _ _ hT
  have hM := famMC_conj k hk _ _ hT
  rw [h0] at hS0
  rw [h2] at hS2
  clear hW1 hW2 hW3 hW4 hW5 hW6 hW7 hH2 hcl hB hf hσ h0 h2
  generalize famOrbitLoop k L = Λ at *
  generalize famG0 k (L (4 * k + 1)) (L (2 * k)) = g at *
  generalize famU k (L (4 * k + 1)) (L (2 * k)) = u at *
  generalize famMC k (L (4 * k + 1)) (L (2 * k)) = M at *
  generalize hlam : compLong k (L (4 * k + 1)) (L (2 * k)) = lam at *
  generalize L (2 * k + 1) = h at *
  generalize L (2 * k) = d at *
  generalize L (4 * k + 1) = c at *
  have hβ : β = g⁻¹ * a * g := by rw [hS0]; group
  have hM' : M = d * g⁻¹ * lam⁻¹ * g * d⁻¹ := by rw [← hM]; group
  have hc : Commute Λ a := hcomm
  have hlΛ : l = a ^ 2 * Λ * (a ^ 2)⁻¹ := by
    rw [hl, ← (hc.zpow_right _).eq, ← (hc.pow_right 2).eq]; group
  subst hM' hlΛ hO hH1
  subst hd
  subst hS2 hβ hGU
  have hcm : compMer a ((g * u)⁻¹ * a * (g * u)) = c := by
    rw [← hU, compMer]; group
  rw [IsSatelliteData, hcm, hlam]
  refine ⟨hT, rfl, ?_⟩
  group

end AJConjecture
