import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaPolynomialTailSummability.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core

/-!
# Completed zero multiplicity counting

This file owns the multiplicity-aware zero-counting surface used by the zero-tail
majorant.  The analytic input is the coarse finite-order/Jensen theorem: completed zeta
zeros, counted with analytic multiplicity, have polynomial growth in centered height.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem singletonSupport_real_value_at_center
    {α : Type*} [DecidableEq α] (u : α → ℝ) (a : α) :
    (if a = a then u a else 0) = u a :=
  if_pos (Eq.refl a)

theorem singletonSupport_real_value_of_eq
    {α : Type*} [DecidableEq α] (u : α → ℝ) (a x : α)
    (hxa : x = a) :
    (if x = a then u a else 0) = u x := by
  have hvalue : (if x = a then u a else 0) = u a := if_pos hxa
  have htransport : u a = u x := congrArg u hxa.symm
  exact Eq.trans hvalue htransport

theorem singletonSupport_real_value_of_ne
    {α : Type*} [DecidableEq α] (u : α → ℝ) (a x : α)
    (hxa : x ≠ a) :
    (if x = a then u a else 0) = 0 :=
  if_neg hxa

theorem singletonSupport_real_le_pointwise
    {α : Type*} [DecidableEq α] (u : α → ℝ)
    (h_nonneg : ∀ x : α, 0 ≤ u x) (a x : α) :
    (if x = a then u a else 0) ≤ u x := by
  exact
    match (inferInstance : Decidable (x = a)) with
    | Decidable.isTrue hxa =>
        Eq.subst
          (motive := fun value : ℝ => value ≤ u x)
          (singletonSupport_real_value_of_eq u a x hxa).symm
          (le_refl (u x))
    | Decidable.isFalse hxa =>
        Eq.subst
          (motive := fun value : ℝ => value ≤ u x)
          (singletonSupport_real_value_of_ne u a x hxa).symm
          (h_nonneg x)

/-- The singleton-supported real family at `a` has sum `u a`. -/
theorem hasSum_singletonSupport_real
    {α : Type*} [DecidableEq α] (u : α → ℝ) (a : α) :
    HasSum
      (fun x : α => if x = a then u a else 0)
      (u a) := by
  have hoff :
      ∀ x : α, x ∉ ({a} : Finset α) →
        (if x = a then u a else 0) = 0 := by
    intro x hx
    have hne : x ≠ a := Finset.not_mem_singleton.mp hx
    exact singletonSupport_real_value_of_ne u a x hne
  have hsum :
      HasSum
        (fun x : α => if x = a then u a else 0)
        (∑ x in ({a} : Finset α), if x = a then u a else 0) :=
    hasSum_sum_of_ne_finset_zero hoff
  have hfinite :
      (∑ x in ({a} : Finset α), if x = a then u a else 0) = u a := by
    have hsingleton :
        (∑ x in ({a} : Finset α), if x = a then u a else 0) =
          (if a = a then u a else 0) :=
      Finset.sum_singleton (fun x : α => if x = a then u a else 0) a
    have hvalue : (if a = a then u a else 0) = u a :=
      singletonSupport_real_value_at_center u a
    exact Eq.trans hsingleton hvalue
  exact Eq.subst
    (motive := fun t : ℝ =>
      HasSum (fun x : α => if x = a then u a else 0) t)
    hfinite
    hsum

/-- A nonnegative summable real family dominates each of its terms by its total `tsum`. -/
theorem real_term_le_tsum_of_summable_nonnegative
    {α : Type*} [DecidableEq α] (u : α → ℝ)
    (hu : Summable u)
    (h_nonneg : ∀ a : α, 0 ≤ u a)
    (a : α) :
    u a ≤ ∑' x : α, u x := by
  let v : α → ℝ := fun x : α => if x = a then u a else 0
  have hv_hasSum : HasSum v (u a) :=
    hasSum_singletonSupport_real u a
  have hv_summable : Summable v :=
    ⟨u a, hv_hasSum⟩
  have hv_tsum : (∑' x : α, v x) = u a :=
    hv_hasSum.tsum_eq
  have hv_le_u : ∀ x : α, v x ≤ u x :=
    fun x => singletonSupport_real_le_pointwise u h_nonneg a x
  have htsum_le :
      (∑' x : α, v x) ≤ ∑' x : α, u x :=
    tsum_le_tsum hv_le_u hv_summable hu
  exact Eq.subst
    (motive := fun t : ℝ => t ≤ ∑' x : α, u x)
    hv_tsum
    htsum_le

/-- Height-ball multiplicity summands are nonnegative. -/
theorem completedZeroMultiplicityHeightBallSummand_nonnegative
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    [Decidable (zetaCompletedZeroCenteredHeight ρ ≤ T)] :
    0 ≤ completedZeroMultiplicityHeightBallSummand T ρ := by
  exact
    match (inferInstance : Decidable (zetaCompletedZeroCenteredHeight ρ ≤ T)) with
    | Decidable.isTrue hρ =>
        Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          (if_pos hρ).symm
          (Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ)))
    | Decidable.isFalse hρ =>
        Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          (if_neg hρ).symm
            (le_refl (0 : ℝ))

theorem completedZeroMultiplicityHeightBallSummand_nonnegative_pointwise
    (T : ℝ) :
    ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
      0 ≤ completedZeroMultiplicityHeightBallSummand T ρ := by
  letI : DecidablePred
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ≤ T) :=
    Classical.decPred
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ≤ T)
  exact fun ρ => completedZeroMultiplicityHeightBallSummand_nonnegative T ρ

theorem completedZeroMultiplicityHeightBallSummand_eq_multiplicity_of_le
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : zetaCompletedZeroCenteredHeight ρ ≤ T) :
    completedZeroMultiplicityHeightBallSummand T ρ =
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
  if_pos hρ

theorem completedZeroMultiplicityHeightBallSummand_eq_zero_of_not_le
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ¬zetaCompletedZeroCenteredHeight ρ ≤ T) :
    completedZeroMultiplicityHeightBallSummand T ρ = 0 :=
  if_neg hρ

theorem completedZeroMultiplicityHeightBallSummand_le_of_both_mem
    {S T : ℝ} (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hS : zetaCompletedZeroCenteredHeight ρ ≤ S)
    (hT : zetaCompletedZeroCenteredHeight ρ ≤ T) :
    completedZeroMultiplicityHeightBallSummand S ρ ≤
      completedZeroMultiplicityHeightBallSummand T ρ := by
  exact Eq.subst
    (motive := fun leftValue : ℝ =>
      leftValue ≤ completedZeroMultiplicityHeightBallSummand T ρ)
    (completedZeroMultiplicityHeightBallSummand_eq_multiplicity_of_le S ρ hS).symm
    (Eq.subst
      (motive := fun rightValue : ℝ =>
        (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤ rightValue)
      (completedZeroMultiplicityHeightBallSummand_eq_multiplicity_of_le T ρ hT).symm
      (le_refl (zetaZeroMultiplicity (ρ : ℂ) : ℝ)))

theorem completedZeroMultiplicityHeightBallSummand_le_of_left_not_mem
    {S T : ℝ} (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hS : ¬zetaCompletedZeroCenteredHeight ρ ≤ S) :
    completedZeroMultiplicityHeightBallSummand S ρ ≤
      completedZeroMultiplicityHeightBallSummand T ρ := by
  have hrightNonnegative :
      0 ≤ completedZeroMultiplicityHeightBallSummand T ρ :=
    completedZeroMultiplicityHeightBallSummand_nonnegative_pointwise T ρ
  exact Eq.subst
    (motive := fun leftValue : ℝ =>
      leftValue ≤ completedZeroMultiplicityHeightBallSummand T ρ)
    (completedZeroMultiplicityHeightBallSummand_eq_zero_of_not_le S ρ hS).symm
    hrightNonnegative

/-- Height-ball summands are monotone in the radius. -/
theorem completedZeroMultiplicityHeightBallSummand_mono
    {S T : ℝ} (hST : S ≤ T)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroMultiplicityHeightBallSummand S ρ ≤
      completedZeroMultiplicityHeightBallSummand T ρ := by
  letI : Decidable (zetaCompletedZeroCenteredHeight ρ ≤ S) :=
    Classical.propDecidable (zetaCompletedZeroCenteredHeight ρ ≤ S)
  exact match (inferInstance : Decidable (zetaCompletedZeroCenteredHeight ρ ≤ S)) with
    | Decidable.isTrue hS =>
        have hT : zetaCompletedZeroCenteredHeight ρ ≤ T :=
          le_trans hS hST
        completedZeroMultiplicityHeightBallSummand_le_of_both_mem ρ hS hT
    | Decidable.isFalse hS =>
        completedZeroMultiplicityHeightBallSummand_le_of_left_not_mem ρ hS


end

end LFunctions
end Boundary
