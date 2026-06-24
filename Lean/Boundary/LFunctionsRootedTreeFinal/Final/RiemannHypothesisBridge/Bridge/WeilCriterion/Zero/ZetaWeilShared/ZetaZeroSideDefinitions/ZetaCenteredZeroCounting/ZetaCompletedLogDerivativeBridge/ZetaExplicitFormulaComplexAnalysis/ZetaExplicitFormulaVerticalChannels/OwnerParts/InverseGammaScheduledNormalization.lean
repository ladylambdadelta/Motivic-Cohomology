import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaComponentNormalizations

/-!
# Inverse-Gamma completion normalization

This file owns the Gamma/Binet normalization of the inverse-Gamma completion
difference on vertically regular contours.  The component whole-line values
live in `InverseGammaComponentNormalizations`; this file recombines them and
transports the whole-line value through scheduled-window exhaustion.
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

/-- Owner analytic leaf: whole-line Gamma/Binet normalization of the
inverse-Gamma difference affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_verticallyRegular_gammaBinet_direct_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
  match
    zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_integrable_and_integral_eq_archimedeanContribution_of_verticallyRegular_gammaBinet_ownerNormalization
      f F h hcoh,
    zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_integrable_and_integral_eq_correctionContribution_of_verticallyRegular_gammaBinet_ownerNormalization
      f F h hcoh with
  | ⟨harch_integrable, harch_value⟩, ⟨hcorr_integrable, hcorr_value⟩ =>
      have hsplit :
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
              f F.toContourFamily t) =
            (∫ t : ℝ,
              zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
                f F.toContourFamily t) +
              ∫ t : ℝ,
                zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
                  f F.toContourFamily t :=
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_integral_add_correction_integral
          f F.toContourFamily harch_integrable hcorr_integrable
      exact
        Eq.trans hsplit
          (congrArg₂ HAdd.hAdd harch_value hcorr_value)

/-- Owner transport theorem: scheduled Gamma/Binet normalization of the
inverse-Gamma difference affine kernel from the whole-line value. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernelIntegral_tendsto_archimedean_add_correction_of_verticallyRegular_gammaBinet_direct_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernelIntegral_tendsto_archimedean_add_correction_direct
      f F.toContourFamily h
      (zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
        F)
      hcoh
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_verticallyRegular_gammaBinet_direct_ownerNormalization
        f F h hcoh)

/-- Public owner wrapper for the whole-line Gamma/Binet normalization of the
inverse-Gamma difference affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_verticallyRegular_gammaBinet_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
  exact
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_verticallyRegular_gammaBinet_direct_ownerNormalization
      f F h hcoh

/-- Owner scheduled inverse-Gamma normalization, exposed under the public owner
name. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernelIntegral_tendsto_archimedean_add_correction_of_verticallyRegular_gammaBinet_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernelIntegral_tendsto_archimedean_add_correction_of_verticallyRegular_gammaBinet_direct_ownerNormalization
      f F h hcoh

/-- Extract the left inverse-Gamma affine value on a vertically regular contour
from a right affine value and the owner right-minus-left normalization.

This theorem does not supply the right affine value.  It records the canonical
component algebra after the difference normalization has been proved. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_rightValue_sub_archimedean_add_correction_of_verticallyRegular_gammaBinet
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (R : ℂ)
    (hright_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          f F.toContourFamily t) = R) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
        f F.toContourFamily t) =
      R -
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hright :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
      f F.toContourFamily h hcoh
  have hleft :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable
      f F.toContourFamily h hregular hcoh
  have hdifference :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f :=
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_verticallyRegular_gammaBinet_ownerNormalization
      f F h hcoh
  exact
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_rightValue_sub_differenceValue
      f F.toContourFamily hright hleft R
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      hright_value hdifference

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
