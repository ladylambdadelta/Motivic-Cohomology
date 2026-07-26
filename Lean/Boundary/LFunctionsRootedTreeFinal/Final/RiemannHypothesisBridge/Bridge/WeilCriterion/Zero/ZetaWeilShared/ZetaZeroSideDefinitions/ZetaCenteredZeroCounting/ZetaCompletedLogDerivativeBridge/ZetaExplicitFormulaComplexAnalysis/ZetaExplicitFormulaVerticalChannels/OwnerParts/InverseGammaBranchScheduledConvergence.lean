import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaBranchKernelConvergence
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanScheduledChannels

/-!
# Branch scheduled inverse-Gamma convergence

This file transports the branch-coherence inverse-Gamma difference-kernel
exhaustion theorem to the scheduled completed inverse-Gamma vertical channel.
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

/-- On a finite symmetric window, the right-minus-left inverse-Gamma affine
integrals are the integral of the right-minus-left affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightSubLeftAffineKernel_windowIntegral_eq_differenceIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hright :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
        (volume : Measure ℝ))
    (hleft :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume : Measure ℝ))
    (T : ℝ) :
    (∫ t in Set.Icc (-T) T,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t =
      ∫ t in Set.Icc (-T) T,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t :=
  explicitFormulaSymmetricIntervalIntegral_sub_eq_integral_sub
    (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
    (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
    hright hleft T

/-- Branch-coherence scheduled convergence of the right-minus-left
inverse-Gamma affine integrals. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_of_branchBinet_regular_and_integral_eq_rightSubLeft
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
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
          ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
  explicitFormulaScheduledScalar_tendsto_of_forall_eq
    (fun u : ℝ =>
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t)
    (fun u : ℝ =>
      ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
    (zetaCompletedExplicitFormulaArchimedeanContribution f +
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
    (zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_of_branchBinet_regular_and_integral_eq
      f F h hregular hbranch hvalue)
    (fun u : ℝ =>
      zetaCompletedExplicitFormulaInverseGammaRightSubLeftAffineKernel_windowIntegral_eq_differenceIntegral
        f F
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_branchBinet
          f F h hbranch).integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_branchBinet
          f F h hregular hbranch).integrable
        ((F.rectangle (h.height_schedule.height u)).T))

/-- The scheduled inverse-Gamma completion channel converges under branch
coherence once the whole-line inverse-Gamma value identity has been proved. -/
theorem zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_archimedean_add_correction_of_branchBinet_regular_and_integral_eq
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
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
  explicitFormulaScheduledScalar_tendsto_of_forall_eq
    (fun u : ℝ =>
      zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
        f F h u)
    (fun u : ℝ =>
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t)
    (zetaCompletedExplicitFormulaArchimedeanContribution f +
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
    (zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_of_branchBinet_regular_and_integral_eq_rightSubLeft
      f F h hregular hbranch hvalue)
    (fun u : ℝ =>
      zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_eq_affineKernelIntegrals
        f F h u)

/-- Vertically regular branch-coherence scheduled inverse-Gamma convergence. -/
theorem zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_archimedean_add_correction_of_verticallyRegular_branchBinet_integral_eq
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
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
  zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_archimedean_add_correction_of_branchBinet_regular_and_integral_eq
    f F.toContourFamily h
    (zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F)
    hbranch hvalue

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
