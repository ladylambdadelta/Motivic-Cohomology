import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleFunction

/-!
# Boundary admissible test functions support helpers

This file packages the reusable support lemmas as direct helper declarations.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

theorem mem_support_iff {f : ZetaAdmissibleFunction} {x : ℝ} :
    x ∈ Function.support f ↔ f x ≠ 0 := by
  rfl

theorem mem_support_of_ne_zero {f : ZetaAdmissibleFunction} {x : ℝ}
    (hx : f x ≠ 0) : x ∈ Function.support f := by
  exact mem_support_iff.mpr hx

theorem ne_zero_of_mem_support {f : ZetaAdmissibleFunction} {x : ℝ}
    (hx : x ∈ Function.support f) : f x ≠ 0 := by
  exact mem_support_iff.mp hx

theorem mem_iUnion_pair {α β : Type*} {s : Finset α} {p : α → Set β} {x : β}
    (hx : x ∈ ⋃ a ∈ s, p a) : ∃ a ∈ s, x ∈ p a := by
  rcases Set.mem_iUnion.1 hx with ⟨a, hx⟩
  rcases Set.mem_iUnion.1 hx with ⟨ha, hpa⟩
  exact ⟨a, ha, hpa⟩

theorem mem_iUnion_pair_of_exists {α β : Type*} {s : Finset α} {p : α → Set β} {x : β}
    (hx : ∃ a ∈ s, x ∈ p a) : x ∈ ⋃ a ∈ s, p a := by
  rcases hx with ⟨a, ha, hpa⟩
  exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hpa⟩⟩

theorem mem_iUnion_pair_iff {α β : Type*} {s : Finset α} {p : α → Set β} {x : β} :
    x ∈ ⋃ a ∈ s, p a ↔ ∃ a ∈ s, x ∈ p a := by
  exact Iff.intro mem_iUnion_pair mem_iUnion_pair_of_exists

theorem exists_nonzero_term_of_sum_ne_zero_at {α : Type*} [DecidableEq α] (s : Finset α)
    (g : α → ZetaAdmissibleFunction) {x : ℝ}
    (hx : (∑ a in s, g a x) ≠ 0) : ∃ a ∈ s, g a x ≠ 0 := by
  exact Finset.exists_ne_zero_of_sum_ne_zero (s := s) (f := fun a => g a x) hx

theorem support_of_smul_term_nonzero {c : ℂ} {f : ZetaAdmissibleFunction} {x : ℝ}
    (hx : (c • f) x ≠ 0) : x ∈ Function.support f := by
  exact mem_support_of_ne_zero (by
    intro hfx
    exact hx (by
      calc
        (c • f) x = c * f x := rfl
        _ = c * 0 := by exact congrArg (fun t => c * t) hfx
        _ = 0 := by exact mul_zero c))

theorem support_sum_subset_finset {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ZetaAdmissibleFunction) :
    Function.support (∑ a in s, f a) ⊆ ⋃ a ∈ s, Function.support (f a) := by
  intro x hx
  have hxfunction :
      (∑ a in s, ⇑(f a).toZetaTestFunction) x ≠ 0 := by
    exact hx
  have hxsum : (∑ a in s, f a x) ≠ 0 := by
    exact Eq.subst (motive := fun y => y ≠ 0)
      (s.sum_apply x (fun a => ⇑(f a).toZetaTestFunction))
      hxfunction
  have hterm : ∃ a ∈ s, f a x ≠ 0 :=
    exists_nonzero_term_of_sum_ne_zero_at (s := s) (g := f) hxsum
  exact mem_iUnion_pair_of_exists
    (p := fun a => Function.support (f a))
    (x := x)
    hterm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
