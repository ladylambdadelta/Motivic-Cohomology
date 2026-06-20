import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroMultiplicityCore.RadialGap.PointwiseComparison.Owner

/-!
# Jensen radial-gap multiplicity core

This owner layer was split from `ZeroMultiplicityCore.RadialGap.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

/-- Non-origin closed-disk multiplicity weighted by `log 2` is dominated by
the doubled-radius Jensen radial-gap sum.

This is the finite/counting part of the Jensen estimate. The analytic Jensen
formula enters only through an upper bound on the radial-gap sum. -/
theorem entireFunctionNonzeroZeroMultiplicityCountingInClosedDisk_mul_log_two_le_radialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    (hR : 1 ≤ R)
    (hclosed :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z))
    (hgap :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF (2 * R) z)) :
    (∑' z : EntireFunctionZero F,
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
        Real.log 2 ≤
      entireFunctionJensenRadialGapSum F hF (2 * R) := by
  change
    (∑' z : EntireFunctionZero F,
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
        Real.log 2 ≤
      ∑' z : EntireFunctionZero F,
        entireFunctionJensenRadialGapSummand F hF (2 * R) z
  have hclosed_scaled :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
            Real.log 2) :=
    hclosed.mul_right (Real.log 2)
  have htsum_mul :
      (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
          Real.log 2 =
        ∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
            Real.log 2 := by
    exact (hclosed.tsum_mul_right (Real.log 2)).symm
  calc
    (∑' z : EntireFunctionZero F,
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
        Real.log 2 =
      ∑' z : EntireFunctionZero F,
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
          Real.log 2 := htsum_mul
    _ ≤
      ∑' z : EntireFunctionZero F,
        entireFunctionJensenRadialGapSummand F hF (2 * R) z :=
      tsum_le_tsum
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_mul_log_two_le_radialGapSummand
            F hF hR z)
        hclosed_scaled
        hgap

/-- Reattaching the origin Taylor factor: the full closed-disk count is bounded
by the non-origin count plus the fixed origin contribution. -/
theorem entireFunctionZeroMultiplicityCountingInClosedDisk_mul_log_two_le_originContribution_plus_nonzeroCount
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    (hR : 1 ≤ R)
    (hclosed :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) :
    entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
      entireFunctionOriginMultiplicityLogContribution F hF +
        (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
            Real.log 2 := by
  have horigin_summable :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) :=
    entireFunctionOriginZeroMultiplicityClosedDiskSummable F hF R
  have hfull_summable :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) :=
    (hclosed.add horigin_summable).congr
      (fun z => by
        exact
          (entireFunctionZeroMultiplicityClosedDiskSummand_eq_nonzero_add_origin
            F hF R z).symm)
  have hcount_split :
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R =
        (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) +
          ∑' z : EntireFunctionZero F,
            entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z := by
    change
      (∑' z : EntireFunctionZero F,
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) =
        (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) +
          ∑' z : EntireFunctionZero F,
            entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z
    calc
      ∑' z : EntireFunctionZero F,
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
          = ∑' z : EntireFunctionZero F,
              (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z +
                entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) := by
              exact tsum_congr (fun z =>
                entireFunctionZeroMultiplicityClosedDiskSummand_eq_nonzero_add_origin F hF R z)
      _ = (∑' z : EntireFunctionZero F,
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) +
          ∑' z : EntireFunctionZero F,
            entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z := by
              exact tsum_add hclosed horigin_summable
  have horigin_bound :
      (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
          Real.log 2 ≤
        entireFunctionOriginMultiplicityLogContribution F hF :=
    entireFunctionOriginZeroMultiplicityClosedDisk_tsum_mul_log_two_le_originContribution
      F hF hR
  have hsplit_mul :
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 =
        (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
            Real.log 2 +
          (∑' z : EntireFunctionZero F,
            entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
            Real.log 2 := by
    have hsplit :
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R =
          (∑' z : EntireFunctionZero F,
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) +
            (∑' z : EntireFunctionZero F,
              entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) := hcount_split
    have hmul :
        ((∑' z : EntireFunctionZero F,
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) +
            (∑' z : EntireFunctionZero F,
              entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z)) *
            Real.log 2 =
          (∑' z : EntireFunctionZero F,
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2 +
            (∑' z : EntireFunctionZero F,
              entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2 := by
      exact add_mul
        (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)
        (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z)
        (Real.log 2)
    calc
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2
          = ((∑' z : EntireFunctionZero F,
              entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) +
              (∑' z : EntireFunctionZero F,
                entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z)) *
              Real.log 2 := by
              exact congrArg (fun t : ℝ => t * Real.log 2) hsplit
      _ =
          (∑' z : EntireFunctionZero F,
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2 +
            (∑' z : EntireFunctionZero F,
              entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2 := hmul
  calc
    entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2
        = (∑' z : EntireFunctionZero F,
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2 +
            (∑' z : EntireFunctionZero F,
              entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2 := hsplit_mul
    _ ≤ (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
            Real.log 2 +
          entireFunctionOriginMultiplicityLogContribution F hF := by
      exact add_le_add_left horigin_bound _
    _ = entireFunctionOriginMultiplicityLogContribution F hF +
          (∑' z : EntireFunctionZero F,
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2 := by
      exact add_comm _ _

/-- Full closed-disk multiplicity weighted by `log 2` is bounded by the
doubled-radius radial-gap sum, up to the fixed origin Taylor contribution. -/
theorem entireFunctionZeroMultiplicityCountingInClosedDisk_mul_log_two_le_originContribution_plus_radialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    (hR : 1 ≤ R)
    (hclosed :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z))
    (hgap :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF (2 * R) z)) :
    entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
      entireFunctionOriginMultiplicityLogContribution F hF +
        entireFunctionJensenRadialGapSum F hF (2 * R) := by
  have horigin :
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
        entireFunctionOriginMultiplicityLogContribution F hF +
          (∑' z : EntireFunctionZero F,
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2 :=
    entireFunctionZeroMultiplicityCountingInClosedDisk_mul_log_two_le_originContribution_plus_nonzeroCount
      F hF hR hclosed
  have hnonzero :
      (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
          Real.log 2 ≤
        entireFunctionJensenRadialGapSum F hF (2 * R) :=
    entireFunctionNonzeroZeroMultiplicityCountingInClosedDisk_mul_log_two_le_radialGapSum
      F hF hR hclosed hgap
  exact le_trans horigin (add_le_add_left hnonzero _)


end
end LFunctions
end Boundary
