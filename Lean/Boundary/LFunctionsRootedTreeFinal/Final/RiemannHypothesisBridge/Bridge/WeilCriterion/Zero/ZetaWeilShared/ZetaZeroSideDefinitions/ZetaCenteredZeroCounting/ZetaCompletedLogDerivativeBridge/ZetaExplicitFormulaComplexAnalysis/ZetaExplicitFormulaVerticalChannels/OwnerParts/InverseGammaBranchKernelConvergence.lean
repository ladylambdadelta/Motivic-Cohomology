import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaBranchAffineKernelEstimate

/-!
# Branch inverse-Gamma kernel convergence

This file owns the branch-coherence version of the inverse-Gamma affine-kernel
exhaustion estimates.  It mirrors the regular Gamma/Binet convergence API, but
uses the Abel-Plana Binet branch coherence package instead of the global
principal-log/slit-plane route.
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

/-- Branch-coherence majorant package for the right-minus-left inverse-Gamma
affine kernel. -/
def zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_majorantPackage_of_branchBinet
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F) :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_branchBinet
    f F h hbranch).sub
    (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_branchBinet
      f F h hregular hbranch)

/-- Branch-coherence integrability of the right-minus-left inverse-Gamma affine
kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_branchBinet_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_majorantPackage_of_branchBinet
    f F h hregular hbranch).integrable

/-- Vertically regular, branch-coherence integrability of the right-minus-left
inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_verticallyRegular_branchBinet
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_branchBinet_regular
    f F.toContourFamily h
    (zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F)
    hbranch

/-- Symmetric-window convergence of the inverse-Gamma difference affine kernel
to its whole-line integral under branch-coherence hypotheses. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_symmetric_of_branchBinet_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) :=
  explicitFormulaSymmetricIntervalIntegral_tendsto_integral
    (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
    (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_branchBinet_regular
      f F h hregular hbranch)

/-- Rectangle-window convergence of the inverse-Gamma difference affine kernel
to its whole-line integral under branch-coherence hypotheses. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_unscheduled_of_branchBinet_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) :=
  explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
    F
    (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
    (zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_symmetric_of_branchBinet_regular
      f F h hregular hbranch)

/-- Scheduled-window convergence of the inverse-Gamma difference affine kernel
to its whole-line integral under branch-coherence hypotheses. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_of_branchBinet_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) :=
  explicitFormulaScheduledScalar_tendsto_of_unscheduled
    (fun T : ℝ =>
      ∫ t in Set.Icc
          (-(F.rectangle T).T)
          (F.rectangle T).T,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
    h.height_schedule.height
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
    (zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_unscheduled_of_branchBinet_regular
      f F h hregular hbranch)
    h.height_schedule.cofinal

/-- Symmetric-window inverse-Gamma completion convergence from branch
coherence and a separately proved whole-line value identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_symmetric_of_branchBinet_regular_and_integral_eq
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
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
  explicitFormulaSymmetricIntervalIntegral_tendsto_value
    (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
    (zetaCompletedExplicitFormulaArchimedeanContribution f +
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
    (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_branchBinet_regular
      f F h hregular hbranch)
    hvalue

/-- Rectangle-window inverse-Gamma completion convergence from branch coherence
and a separately proved whole-line value identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_unscheduled_of_branchBinet_regular_and_integral_eq
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
      (fun T : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
  explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
    F
    (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
    (zetaCompletedExplicitFormulaArchimedeanContribution f +
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
    (zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_symmetric_of_branchBinet_regular_and_integral_eq
      f F h hregular hbranch hvalue)

/-- Scheduled-window inverse-Gamma completion convergence from branch coherence
and a separately proved whole-line value identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_of_branchBinet_regular_and_integral_eq
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
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
  explicitFormulaScheduledScalar_tendsto_of_unscheduled
    (fun T : ℝ =>
      ∫ t in Set.Icc
          (-(F.rectangle T).T)
          (F.rectangle T).T,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
    h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanContribution f +
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
    (zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_unscheduled_of_branchBinet_regular_and_integral_eq
      f F h hregular hbranch hvalue)
    h.height_schedule.cofinal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
