import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanBranchVerticalAnalyticEstimates

/-!
# Branch archimedean transport

This file owns the branch-coherence transport wrappers for the archimedean
vertical channel and its affine-kernel projections.
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

/-- Branch owner transport theorem for the scheduled Gamma/completion vertical
channel. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerBranchTransport
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
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
  zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_scheduledInverseGammaCompletion_and_scheduledCorrection
    f F h
    (zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_branchBinet_integral_eq
      f F h hregular hbranch hvalue).1
    (zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_branchBinet_integral_eq
      f F h hregular hbranch hvalue).2

/-- Vertically regular branch archimedean-channel transport. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_verticallyRegular_branchBinet_integral_eq
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
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
  zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_scheduledInverseGammaCompletion_and_scheduledCorrection
    f F.toContourFamily h
    (zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_verticallyRegular_branchBinet_integral_eq
      f F h hbranch hvalue).1
    (zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_verticallyRegular_branchBinet_integral_eq
      f F h hbranch hvalue).2

/-- Branch vertically regular scheduled right-minus-left archimedean affine
window convergence. -/
theorem zetaCompletedExplicitFormulaArchimedeanAffineWindowDifference_tendsto_archimedeanContribution_of_verticallyRegular_branchBinet_integral_eq
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
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) -
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
  zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_scheduledWindow_tendsto_of_verticalChannel
    f F.toContourFamily h
    (zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_verticallyRegular_branchBinet_integral_eq
      f F h hbranch hvalue)

/-- Branch vertically regular paired scheduled affine values from the right
scheduled affine value and inverse-Gamma difference normalization. -/
theorem zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_right_and_verticallyRegular_branchBinet_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaPhi f 0 -
            zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
  zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_right_and_difference
    f F.toContourFamily h hright
    (zetaCompletedExplicitFormulaArchimedeanAffineWindowDifference_tendsto_archimedeanContribution_of_verticallyRegular_branchBinet_integral_eq
      f F h hbranch hvalue)

/-- Branch owner transport-remainder form of the archimedean channel estimate. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerBranchTransport
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
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) :=
  zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_of_channel_tendsto_archimedeanContribution
    f F h
    (zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerBranchTransport
      f F h hregular hbranch hvalue)

/-- Vertically regular branch transport-remainder form of the archimedean
channel estimate. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_of_verticallyRegular_branchBinet_integral_eq
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
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) :=
  zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_of_channel_tendsto_archimedeanContribution
    f F.toContourFamily h
    (zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_verticallyRegular_branchBinet_integral_eq
      f F h hbranch hvalue)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
