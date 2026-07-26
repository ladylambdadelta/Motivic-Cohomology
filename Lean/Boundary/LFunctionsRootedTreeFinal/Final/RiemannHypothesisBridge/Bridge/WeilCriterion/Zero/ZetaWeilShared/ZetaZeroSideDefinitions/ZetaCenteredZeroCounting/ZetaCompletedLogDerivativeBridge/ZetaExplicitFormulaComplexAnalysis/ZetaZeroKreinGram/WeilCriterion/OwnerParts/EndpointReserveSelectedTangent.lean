import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.EndpointReservePositivity

/-!
# Endpoint reserve selected-tangent positivity

This owner part peels the selected tangent-residue zero-side endpoint out of
the endpoint-reserve positivity assembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

theorem zetaWeilQuadraticPositivity_of_polynomialScheduledSelectedTangentAffineChannelLimit_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((hPolynomial f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_polynomialScheduledTangentAffineChannelLimit_owner
    hPolynomial
    (fun f =>
      ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_polynomialScheduledPackage_selected
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        (hPolynomial f))
    channelBoundaryLimit

theorem zetaWeilQuadraticPositivity_of_polynomialScheduledSelectedTangentAffineKernelIntegrableValue_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_polynomialScheduledSelectedTangentAffineChannelLimit_owner
    hPolynomial
    (fun f =>
      zetaCompletedScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        (hPolynomial f).height_schedule
        (rightIntegrable f)
        (leftIntegrable f)
        (valueEquality f))

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_selectedTangentAffineChannelLimit_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (C : ZetaAdmissibleFunction → ℝ)
    (C_pos : ∀ f : ZetaAdmissibleFunction, 0 < C f)
    (topBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTopPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (bottomBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBottomPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_pathBounds
                f (K f) (C f) (C_pos f) (topBound f) (bottomBound f)).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_polynomialScheduledSelectedTangentAffineChannelLimit_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_pathBounds
        f
        (K f)
        (C f)
        (C_pos f)
        (topBound f)
        (bottomBound f))
    channelBoundaryLimit

end

end LFunctions
end Boundary
