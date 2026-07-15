import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualBaseWeightedRun

/-!
# Telescoping count of jumps of an integer-valued monotone sequence

For an antitone integer sequence, every strict change consumes at least one
unit of endpoint variation.  This owner packages that elementary fact for the
branch-boundary count of the dual base action.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Int.forwardJumpIndicator
    (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  if f n = f (n + 1) then 0 else 1

def Int.forwardJumpCount
    (f : ℕ → ℤ) (K N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range N,
    Int.forwardJumpIndicator f (K + j)

theorem Int.forwardJumpIndicator_nonneg
    (f : ℕ → ℤ) (n : ℕ) :
    0 ≤ Int.forwardJumpIndicator f n := by
  unfold Int.forwardJumpIndicator
  by_cases h : f n = f (n + 1)
  · exact Eq.subst (motive := fun z : ℤ => 0 ≤ z)
      (if_pos h).symm (Int.le_refl 0)
  · exact Eq.subst (motive := fun z : ℤ => 0 ≤ z)
      (if_neg h).symm Int.zero_le_one

theorem Int.forwardJumpIndicator_eq_zero_of_eq
    (f : ℕ → ℤ) (n : ℕ) (h : f n = f (n + 1)) :
    Int.forwardJumpIndicator f n = 0 := by
  unfold Int.forwardJumpIndicator
  exact if_pos h

theorem Int.forwardJumpIndicator_eq_one_of_ne
    (f : ℕ → ℤ) (n : ℕ) (h : f n ≠ f (n + 1)) :
    Int.forwardJumpIndicator f n = 1 := by
  unfold Int.forwardJumpIndicator
  exact if_neg h

theorem Int.one_le_sub_of_gt
    {a b : ℤ} (h : b < a) :
    1 ≤ a - b := by
  exact Int.add_one_le_iff.mpr
    (Eq.subst (motive := fun z : ℤ => b < z)
      (sub_add_cancel a b).symm h)

theorem Int.forwardJumpIndicator_le_drop
    (f : ℕ → ℤ) (n : ℕ)
    (hanti : f (n + 1) ≤ f n) :
    Int.forwardJumpIndicator f n ≤ f n - f (n + 1) := by
  match eq_or_lt_of_le hanti with
  | Or.inl heq =>
      have hindicator := Int.forwardJumpIndicator_eq_zero_of_eq
        f n heq.symm
      have hdrop : f n - f (n + 1) = 0 := sub_eq_zero.mpr heq.symm
      exact Eq.subst (motive := fun z : ℤ => z ≤ _)
        hindicator.symm
        (Eq.subst (motive := fun z : ℤ => 0 ≤ z)
          hdrop.symm (Int.le_refl 0))
  | Or.inr hlt =>
      have hne : f n ≠ f (n + 1) := ne_of_gt hlt
      have hindicator := Int.forwardJumpIndicator_eq_one_of_ne f n hne
      exact Eq.subst (motive := fun z : ℤ => z ≤ _)
        hindicator.symm (Int.one_le_sub_of_gt hlt)

theorem Int.sum_range_shifted_forwardDrop
    (f : ℕ → ℤ) (K N : ℕ) :
    (∑ j ∈ Finset.range N,
      (f (K + j) - f (K + j + 1))) =
        f K - f (K + N) := by
  have htel := Finset.sum_range_forwardDifference
    (fun j : ℕ => f (K + j)) N
  have hzero : K + 0 = K := Nat.add_zero K
  exact Eq.trans htel
    (congrArg₂ (fun x y : ℤ => x - y)
      (congrArg f hzero) rfl)

theorem Int.forwardJumpCount_le_endpointDrop
    (f : ℕ → ℤ) (K N : ℕ)
    (hanti : ∀ j < N, f (K + j + 1) ≤ f (K + j)) :
    Int.forwardJumpCount f K N ≤ f K - f (K + N) := by
  unfold Int.forwardJumpCount
  have hpoint :
      (∑ j ∈ Finset.range N,
        Int.forwardJumpIndicator f (K + j)) ≤
      ∑ j ∈ Finset.range N,
        (f (K + j) - f (K + j + 1)) := by
    exact Finset.sum_le_sum
      (fun j hj => Int.forwardJumpIndicator_le_drop f (K + j)
        (hanti j (Finset.mem_range.mp hj)))
  exact le_trans hpoint
    (le_of_eq (Int.sum_range_shifted_forwardDrop f K N))

theorem Int.forwardJumpCount_nonneg
    (f : ℕ → ℤ) (K N : ℕ) :
    0 ≤ Int.forwardJumpCount f K N := by
  unfold Int.forwardJumpCount
  exact Finset.sum_nonneg
    (fun j hj => Int.forwardJumpIndicator_nonneg f (K + j))

end

end LFunctions
end Boundary
