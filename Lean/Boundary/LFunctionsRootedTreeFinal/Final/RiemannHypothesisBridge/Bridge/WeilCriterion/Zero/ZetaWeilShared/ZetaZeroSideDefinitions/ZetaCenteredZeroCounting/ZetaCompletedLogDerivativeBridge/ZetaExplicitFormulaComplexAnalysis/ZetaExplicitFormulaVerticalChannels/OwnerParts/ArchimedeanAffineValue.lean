import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineKernelIntegrability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleAffineKernelIntegrability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanScheduledValue

/-!
# Archimedean affine component value

This file owns the value theorem for the archimedean part of the
right-minus-left inverse-Gamma completion kernel.  Integrability and additive
recombination with other components live downstream in
`InverseGammaComponentNormalizations`.
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

/-- Integrability of the archimedean right-minus-left affine kernel under
vertical regularity and Gamma/Binet coherence.

This majorant theorem is upstream of the component-normalization assembly.  It
uses the pointwise identity
`archimedean = inverseGammaDifference - correctionDifference`, the Gamma/Binet
majorant for the inverse-Gamma difference kernel, and the elementary
pole-kernel majorants for the correction term. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_integrable_of_verticallyRegular_gammaBinet_ownerAffineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) := by
  have hinv :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_owner
      f F.toContourFamily h
      (zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
        F)
      hcoh
  have hright_zero :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hright_one :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hright_sum :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
              f F.toContourFamily t)
        (volume : Measure ℝ) :=
    hright_zero.add hright_one
  have hright_point :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightAffineKernel
          f F.toContourFamily t) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaCorrectionRightAffineKernel_eq_zeroPole_add_onePole
          f F.toContourFamily t)
  have hright :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    hright_sum.congr hright_point.symm
  have hleft_zero :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hleft_one :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hleft_sum :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
              f F.toContourFamily t)
        (volume : Measure ℝ) :=
    hleft_zero.add hleft_one
  have hleft_point :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
          f F.toContourFamily t) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_eq_zeroPole_add_onePole
          f F.toContourFamily t)
  have hleft :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    hleft_sum.congr hleft_point.symm
  have hcorr :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    hright.sub hleft
  have hdiff :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
            f F.toContourFamily t -
            zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
              f F.toContourFamily t)
        (volume : Measure ℝ) :=
    hinv.sub hcorr
  have hpoint :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
          f F.toContourFamily t) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
            f F.toContourFamily t -
            zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_eq_inverseGamma_sub_correction
          f F.toContourFamily t)
  exact hdiff.congr hpoint.symm

/-- Compatibility name for the scheduled-window archimedean Gamma/Binet value
owned in `ArchimedeanScheduledValue`. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_scheduledWindow_tendsto_archimedeanContribution_ownerAffineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_scheduledWindow_tendsto_archimedeanContribution_ownerScheduledValue
      f F h hcoh

/-- Owner value theorem: whole-line value of the archimedean right-minus-left
affine kernel.

This theorem is only exhaustion transport from the scheduled Gamma/Binet value
leaf to the whole-line affine integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_integral_eq_archimedeanContribution_ownerAffineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaArchimedeanContribution f := by
  exact
    explicitFormulaScheduledRectangleWindowIntegral_eq_of_tendsto_value
      F.toContourFamily
      h.height_schedule.height
      (zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
        f F.toContourFamily)
      (zetaCompletedExplicitFormulaArchimedeanContribution f)
      h.height_schedule.cofinal
      (zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_integrable_of_verticallyRegular_gammaBinet_ownerAffineValue
        f F h hcoh)
      (zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_scheduledWindow_tendsto_archimedeanContribution_ownerAffineValue
        f F h hcoh)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
