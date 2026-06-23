import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroMultiplicityCore.Basic.Owner

/-!
# Entire-function closed-disk zero counting core

This owner layer was split from `ZeroMultiplicityCore.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

/-- Multiplicity summand for entire-function zeros inside a closed disk. -/
noncomputable def entireFunctionZeroMultiplicityClosedDiskSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    (z : EntireFunctionZero F) : ℝ :=
  if ‖(z : ℂ)‖ ≤ R then
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
  else
    0

/-- Multiplicity count for entire-function zeros inside a closed disk. -/
noncomputable def entireFunctionZeroMultiplicityCountingInClosedDisk
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)] : ℝ :=
  ∑' z : EntireFunctionZero F,
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z

/-- Entire-function closed-disk multiplicity summands are nonnegative. -/
theorem entireFunctionZeroMultiplicityClosedDiskSummand_nonnegative
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    (z : EntireFunctionZero F) :
    0 ≤ entireFunctionZeroMultiplicityClosedDiskSummand F hF R z := by
  show
    0 ≤
      if ‖(z : ℂ)‖ ≤ R then
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
      else
        0
  match (inferInstance : Decidable (‖(z : ℂ)‖ ≤ R)) with
  | isTrue hz =>
      exact Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        (if_pos hz).symm
        (Nat.cast_nonneg (entireFunctionZeroMultiplicity F hF (z : ℂ)))
  | isFalse hz =>
      exact Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        (if_neg hz).symm
        (le_refl (0 : ℝ))

/-- Entire-function closed-disk multiplicity summands are monotone in the disk radius. -/
theorem entireFunctionZeroMultiplicityClosedDiskSummand_mono
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R S : ℝ}
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ S)]
    (hRS : R ≤ S)
    (z : EntireFunctionZero F) :
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z ≤
      entireFunctionZeroMultiplicityClosedDiskSummand F hF S z := by
  show
    (if ‖(z : ℂ)‖ ≤ R then
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
      else
        0) ≤
      if ‖(z : ℂ)‖ ≤ S then
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
      else
        0
  match (inferInstance : Decidable (‖(z : ℂ)‖ ≤ R)) with
  | isTrue hzR =>
      have hzS : ‖(z : ℂ)‖ ≤ S :=
        le_trans hzR hRS
      exact Eq.subst
        (motive := fun x : ℝ =>
          x ≤ if ‖(z : ℂ)‖ ≤ S then
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) else 0)
        (if_pos hzR).symm
        (Eq.subst
          (motive := fun x : ℝ =>
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) ≤ x)
          (if_pos hzS).symm
          (le_refl (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)))
  | isFalse hzR =>
      exact Eq.subst
        (motive := fun x : ℝ =>
          x ≤ if ‖(z : ℂ)‖ ≤ S then
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) else 0)
        (if_neg hzR).symm
        (entireFunctionZeroMultiplicityClosedDiskSummand_nonnegative F hF S z)

/-- Entire-function closed-disk multiplicity counts are monotone when the two summand
families are summable. The analytic Jensen root supplies such finiteness in applications. -/
theorem entireFunctionZeroMultiplicityCountingInClosedDisk_mono_of_summable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R S : ℝ}
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ S)]
    (hRS : R ≤ S)
    (hR :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z))
    (hS :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionZeroMultiplicityClosedDiskSummand F hF S z)) :
    entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF S := by
  show
    (∑' z : EntireFunctionZero F,
      entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) ≤
    ∑' z : EntireFunctionZero F,
      entireFunctionZeroMultiplicityClosedDiskSummand F hF S z
  exact tsum_le_tsum
    (fun z : EntireFunctionZero F =>
      entireFunctionZeroMultiplicityClosedDiskSummand_mono F hF hRS z)
    hR
    hS

end
end LFunctions
end Boundary
