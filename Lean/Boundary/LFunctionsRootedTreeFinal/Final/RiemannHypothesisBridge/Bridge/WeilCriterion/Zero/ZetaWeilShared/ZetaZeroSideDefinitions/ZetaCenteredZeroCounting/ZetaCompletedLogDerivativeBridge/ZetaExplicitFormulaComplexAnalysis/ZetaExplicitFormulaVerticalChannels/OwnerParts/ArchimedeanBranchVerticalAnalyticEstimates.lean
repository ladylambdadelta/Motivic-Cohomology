import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanVerticalAnalyticEstimates
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaBranchScheduledConvergence

/-!
# Branch archimedean vertical analytic estimates

This file owns the branch-coherence version of the scheduled archimedean
vertical-channel estimates.  The correction-channel input is unchanged; only
the inverse-Gamma convergence hypothesis is transported to the Abel-Plana Binet
branch.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Combined archimedean scheduled analytic estimates from branch coherence. -/
theorem zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_branchBinet_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
      Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
              f F h u)
          atTop
          (𝓝
            (zetaCompletedExplicitFormulaArchimedeanContribution f +
              zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
              f F h u)
          atTop
          (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
  zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_inverseGamma_and_rightOnePoleProjection
    f F h
    (zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_archimedean_add_correction_of_branchBinet_regular_and_integral_eq
      f F h hregular hbranch hvalue)
    (zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledVerticalIntegral_tendsto_projection
      f F h)

/-- Combined branch-coherence archimedean scheduled analytic estimates for a
vertically regular contour family. -/
theorem zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_verticallyRegular_branchBinet_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
      Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
              f F.toContourFamily h u)
          atTop
          (𝓝
            (zetaCompletedExplicitFormulaArchimedeanContribution f +
              zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
              f F.toContourFamily h u)
          atTop
          (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
  zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_branchBinet_integral_eq
    f F.toContourFamily h
    (zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F)
    hbranch hvalue

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
