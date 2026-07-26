import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathCompletedBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalScheduledBoundaryLimit

/-!
# Affine channel limits for canonical Cauchy path packages

This file owns the passage from full-line affine-kernel integrability and value
identification to the scheduled affine-channel limit for the canonical Cauchy
path package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Full-line affine-kernel integrability and value identification give the
scheduled affine-channel limit for the canonical fixed-degree path-bound
package. -/
theorem zetaCompletedAffineChannel_tendsto_physical_of_canonicalScheduledPathBounds_integrable_value
    (f : ZetaAdmissibleFunction) (K : ℕ) (C : ℝ)
    (C_pos : 0 < C)
    (topBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (bottomBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (rightIntegrable :
      Integrable
        (zetaCompletedRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftIntegrable :
      Integrable
        (zetaCompletedLeftAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (valueEquality :
      (∫ t : ℝ,
          zetaCompletedRightAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) -
        (∫ t : ℝ,
          zetaCompletedLeftAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
          explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel
              (convolutionAutocorrelation f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedAffineVerticalChannel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          ((zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_pathBounds
            f K C C_pos topBound bottomBound).height_schedule.height u))
      atTop
      (𝓝
        (explicitFormulaTwoPi *
          zetaCompletedAffinePhysicalBoundaryChannel
            (convolutionAutocorrelation f))) :=
  zetaCompletedScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_pathBounds
      f K C C_pos topBound bottomBound).height_schedule
    rightIntegrable
    leftIntegrable
    valueEquality

/-- Full-line affine-kernel integrability and value identification give the
scheduled affine-channel limit for the canonical Cauchy path package. -/
theorem zetaCompletedAffineChannel_tendsto_physical_of_canonicalScheduledCauchyPathData_integrable_value
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (zetaData : CanonicalScheduledZetaSideCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaCauchyPathData f K)
    (rightIntegrable :
      Integrable
        (zetaCompletedRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftIntegrable :
      Integrable
        (zetaCompletedLeftAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (valueEquality :
      (∫ t : ℝ,
          zetaCompletedRightAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) -
        (∫ t : ℝ,
          zetaCompletedLeftAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
          explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel
              (convolutionAutocorrelation f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedAffineVerticalChannel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          ((zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
            f K zetaData gammaData).height_schedule.height u))
      atTop
      (𝓝
        (explicitFormulaTwoPi *
          zetaCompletedAffinePhysicalBoundaryChannel
            (convolutionAutocorrelation f))) :=
  zetaCompletedScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
      f K zetaData gammaData).height_schedule
    rightIntegrable
    leftIntegrable
    valueEquality

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
