import Boundary.LFunctions.ZetaAdmissibleFunction

/-!
# Boundary admissible test functions support helpers

This file packages the reusable support lemmas as direct helper declarations.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

theorem support_sum_subset_finset {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    Function.support (∑ a in s, f a) ⊆ ⋃ a ∈ s, Function.support (f a) := by
  intro x hx
  rw [Function.mem_support] at hx
  have hne : ∃ a ∈ s, f a x ≠ 0 := by
    exact Finset.exists_ne_zero_of_sum_ne_zero (s := s) (f := fun a => f a x) (by
      simpa [Finset.sum_apply] using hx)
  rcases hne with ⟨a, ha, hax⟩
  exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hax⟩⟩

theorem support_sum_smul_subset_finset {α : Type*} [DecidableEq α] (s : Finset α)
    (c : α → ℂ) (f : α → ZetaAdmissibleFunction) :
    let g : α → ZetaAdmissibleFunction := fun a => (c a : ℂ) • (f a : ZetaAdmissibleFunction)
    Function.support (∑ a in s, g a) ⊆ ⋃ a ∈ s, Function.support (f a) := by
  dsimp
  intro x hx
  rw [Function.mem_support] at hx
  have hne : ∃ a ∈ s, (c a) * f a x ≠ 0 := by
    exact Finset.exists_ne_zero_of_sum_ne_zero (s := s) (f := fun a => (c a) * f a x) (by
      simpa [Finset.sum_apply, Pi.smul_apply] using hx)
  rcases hne with ⟨a, ha, hax⟩
  have hfa : f a x ≠ 0 := by
    intro hfa
    exact hax (by rw [hfa, mul_zero])
  exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hfa⟩⟩

theorem support_sum_eq_of_pairwise_finset {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaAdmissibleFunction)
    (hdisjoint : Pairwise (fun i j => Disjoint (Function.support (f i))
      (Function.support (f j)))) :
    Function.support (∑ a in s, f a) = ⋃ a ∈ s, Function.support (f a) := by
  refine le_antisymm (support_sum_subset_finset (s := s) (f := f)) ?_
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨a, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨ha, hax⟩
  by_contra hsum
  have hzero : ∀ b ∈ s, b ≠ a → f b x = 0 := by
    intro b hb hba
    by_contra hfb
    have hxb : x ∈ Function.support (f b) := by
      rw [Function.mem_support]
      exact hfb
    have hdisj := hdisjoint (by exact hba)
    exact (Set.disjoint_left.mp hdisj) hxb hax
  have hsum' : (∑ b in s, f b) x = f a x := by
    rw [Finset.sum_eq_single a]
    · rfl
    · intro b hb hba
      exact hzero b hb hba
  exact hsum (by
    rw [Function.mem_support]
    intro hfa
    exact hax (hsum'.trans hfa))

theorem support_sum_smul_eq_of_pairwise_finset {α : Type*} [DecidableEq α] (s : Finset α)
    (c : α → ℂ) (f : α → ZetaAdmissibleFunction)
    (hdisjoint : Pairwise (fun i j => Disjoint (Function.support (f i))
      (Function.support (f j)))) :
    let g : α → ZetaAdmissibleFunction := fun a => (c a : ℂ) • (f a : ZetaAdmissibleFunction)
    Function.support (∑ a in s, g a) = ⋃ a ∈ s, Function.support (g a) := by
  dsimp
  refine le_antisymm (support_sum_smul_subset_finset (s := s) (c := c) (f := f)) ?_
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨a, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨ha, hax⟩
  by_contra hsum
  have hzero : ∀ b ∈ s, b ≠ a → f b x = 0 := by
    intro b hb hba
    by_contra hfb
    have hxb : x ∈ Function.support (f b) := by
      rw [Function.mem_support]
      exact hfb
    have hdisj := hdisjoint (by exact hba)
    exact (Set.disjoint_left.mp hdisj) hxb hax
  have hsum' : (∑ b in s, c b • f b) x = c a • f a x := by
    rw [Finset.sum_eq_single a]
    · rfl
    · intro b hb hba
      rw [Pi.smul_apply, hzero b hb hba, smul_zero]
  exact hsum (by
    rw [Function.mem_support]
    intro hfa
    exact hax (by
      rw [hsum', hfa]
      rfl))

theorem support_sum_fin_eq' (n : ℕ) (f : Fin n → ZetaAdmissibleFunction)
    (hdisjoint : Pairwise (fun i j => Disjoint (Function.support (f i))
      (Function.support (f j)))) :
    Function.support (∑ i, f i) = ⋃ i, Function.support (f i) := by
  simpa using support_sum_eq_of_pairwise_finset (s := Finset.univ) (f := f) hdisjoint

theorem mem_support_sum_iff_of_pairwise {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaAdmissibleFunction)
    (hdisjoint : Pairwise (fun i j => Disjoint (Function.support (f i))
      (Function.support (f j)))) (x : ℝ) :
    x ∈ Function.support (∑ a in s, f a) ↔ ∃ a ∈ s, x ∈ Function.support (f a) := by
  exact Iff.intro
    (fun hx => by
      rw [support_sum_eq_of_pairwise_finset (s := s) (f := f) hdisjoint] at hx
      exact Set.mem_iUnion.1 hx)
    (fun hx => by
      rw [support_sum_eq_of_pairwise_finset (s := s) (f := f) hdisjoint]
      exact Set.mem_iUnion.2 hx)

theorem mem_support_sum_smul_iff_of_pairwise {α : Type*} [DecidableEq α] (s : Finset α)
    (c : α → ℂ) (f : α → ZetaAdmissibleFunction)
    (hdisjoint : Pairwise (fun i j => Disjoint (Function.support (f i))
      (Function.support (f j)))) (x : ℝ) :
    let g : α → ZetaAdmissibleFunction := fun a => (c a : ℂ) • (f a : ZetaAdmissibleFunction)
    x ∈ Function.support (∑ a in s, g a) ↔ ∃ a ∈ s, x ∈ Function.support (g a) := by
  dsimp
  exact Iff.intro
    (fun hx => by
      rw [support_sum_smul_eq_of_pairwise_finset (s := s) (c := c) (f := f) hdisjoint] at hx
      exact Set.mem_iUnion.1 hx)
    (fun hx => by
      rw [support_sum_smul_eq_of_pairwise_finset (s := s) (c := c) (f := f) hdisjoint]
      exact Set.mem_iUnion.2 hx)

theorem mem_support_sum_fin_iff {n : ℕ} (f : Fin n → ZetaAdmissibleFunction)
    (hdisjoint : Pairwise (fun i j => Disjoint (Function.support (f i))
      (Function.support (f j)))) (x : ℝ) :
    x ∈ Function.support (∑ i, f i) ↔ ∃ i, x ∈ Function.support (f i) := by
  exact Iff.intro
    (fun hx => by
      rw [support_sum_fin_eq' (n := n) (f := f) hdisjoint] at hx
      exact Set.mem_iUnion.1 hx)
    (fun hx => by
      rw [support_sum_fin_eq' (n := n) (f := f) hdisjoint]
      exact Set.mem_iUnion.2 hx)

theorem mem_support_sum_smul_fin_iff {n : ℕ} (c : Fin n → ℂ) (f : Fin n → ZetaAdmissibleFunction)
    (hdisjoint : Pairwise (fun i j => Disjoint (Function.support (f i))
      (Function.support (f j)))) (x : ℝ) :
    let g : Fin n → ZetaAdmissibleFunction := fun i => (c i : ℂ) • (f i : ZetaAdmissibleFunction)
    x ∈ Function.support (∑ i, g i) ↔ ∃ i, x ∈ Function.support (g i) := by
  dsimp
  exact Iff.intro
    (fun hx => by
      rw [support_sum_smul_eq_of_pairwise_finset (s := Finset.univ) (c := c) (f := f) hdisjoint] at hx
      exact Set.mem_iUnion.1 hx)
    (fun hx => by
      rw [support_sum_smul_eq_of_pairwise_finset (s := Finset.univ) (c := c) (f := f) hdisjoint]
      exact Set.mem_iUnion.2 hx)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
