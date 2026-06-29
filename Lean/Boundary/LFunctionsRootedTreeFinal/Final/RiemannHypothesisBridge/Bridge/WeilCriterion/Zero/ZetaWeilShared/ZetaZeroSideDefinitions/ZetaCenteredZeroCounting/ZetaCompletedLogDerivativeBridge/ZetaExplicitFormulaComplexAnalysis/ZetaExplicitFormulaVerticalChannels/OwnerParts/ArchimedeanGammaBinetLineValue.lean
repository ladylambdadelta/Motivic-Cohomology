import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetLineCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaOneSidedValues

/-!
# Archimedean Gamma/Binet line values

This file owns the lower wrappers that recover the individual archimedean
line values from one-sided inverse-Gamma normalizations.  The upstream
Gamma/Binet definitions, majorants, and conditional Binet assembly live in
`ArchimedeanGammaBinetLineCore.lean`.
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

theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_inverseGamma_sub_correctionIntegral
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          f F.toContourFamily t) -
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightAffineKernel
            f F.toContourFamily t := by
  have harch :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integrable_ownerGammaBinetLineValue
      f F h hcoh
  have hcorr :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightAffineKernel_integrable_ownerGammaBinetLineValue
      f F.toContourFamily h
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t +
          zetaCompletedExplicitFormulaCorrectionRightAffineKernel
            f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel
              f F.toContourFamily t :=
    integral_add harch hcorr
  have hpoint :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t +
          zetaCompletedExplicitFormulaCorrectionRightAffineKernel
            f F.toContourFamily t) =ᵐ[volume]
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          f F.toContourFamily :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_add_correction_eq_inverseGamma
          f F.toContourFamily t)
  have htotal :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel
              f F.toContourFamily t := by
    exact Eq.trans (integral_congr_ae hpoint.symm) hsum
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
        ((∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel
              f F.toContourFamily t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel
              f F.toContourFamily t := by
      exact (add_sub_cancel
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightAffineKernel
            f F.toContourFamily t)).symm
    _ =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            f F.toContourFamily t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel
              f F.toContourFamily t := by
      exact congrArg
        (fun z : ℂ =>
          z -
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                f F.toContourFamily t)
        htotal.symm

/-- Whole-line left archimedean affine integral as inverse-Gamma minus
elementary correction. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_inverseGamma_sub_correctionIntegral
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily t) -
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
            f F.toContourFamily t := by
  have harch :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integrable_ownerGammaBinetLineValue
      f F h hcoh
  have hcorr :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_integrable_ownerGammaBinetLineValue
      f F.toContourFamily h
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t +
          zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
            f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
              f F.toContourFamily t :=
    integral_add harch hcorr
  have hpoint :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t +
          zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
            f F.toContourFamily t) =ᵐ[volume]
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_add_correction_eq_inverseGamma
          f F.toContourFamily t)
  have htotal :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
              f F.toContourFamily t := by
    exact Eq.trans (integral_congr_ae hpoint.symm) hsum
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
        ((∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
              f F.toContourFamily t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
              f F.toContourFamily t := by
      exact (add_sub_cancel
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
            f F.toContourFamily t)).symm
    _ =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
            f F.toContourFamily t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
              f F.toContourFamily t := by
      exact congrArg
        (fun z : ℂ =>
          z -
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                f F.toContourFamily t)
        htotal.symm

/-- Right archimedean affine line value from separately proved right
inverse-Gamma and correction affine values. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_inverseGamma_and_correction_values
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (G C : ℂ)
    (hinverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          f F.toContourFamily t) = G)
    (hcorrection_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightAffineKernel
          f F.toContourFamily t) = C)
    (hvalue :
      G - C = zetaCompletedExplicitFormulaPhi f 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 := by
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            f F.toContourFamily t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel
              f F.toContourFamily t := by
      exact
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_inverseGamma_sub_correctionIntegral
          f F h hcoh
    _ =
        G -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel
              f F.toContourFamily t := by
      exact congrArg
        (fun z : ℂ =>
          z -
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                f F.toContourFamily t)
        hinverse_value
    _ = G - C := by
      exact congrArg (fun z : ℂ => G - z) hcorrection_value
    _ = zetaCompletedExplicitFormulaPhi f 0 := by
      exact hvalue

/-- Left archimedean affine line value from separately proved left
inverse-Gamma and correction affine values. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_of_inverseGamma_and_correction_values
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (G C : ℂ)
    (hinverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily t) = G)
    (hcorrection_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
          f F.toContourFamily t) = C)
    (hvalue :
      G - C = -(zetaCompletedExplicitFormulaPhi f 0)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
            f F.toContourFamily t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
              f F.toContourFamily t := by
      exact
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_inverseGamma_sub_correctionIntegral
          f F h hcoh
    _ =
        G -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
              f F.toContourFamily t := by
      exact congrArg
        (fun z : ℂ =>
          z -
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                f F.toContourFamily t)
        hinverse_value
    _ = G - C := by
      exact congrArg (fun z : ℂ => G - z) hcorrection_value
    _ = -(zetaCompletedExplicitFormulaPhi f 0) := by
      exact hvalue

/-- Right archimedean affine line value after the correction affine value has
been discharged in its owner file.  The remaining input is the right
inverse-Gamma affine value with the resulting scalar normalization. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_inverseGammaRightValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (G : ℂ)
    (hinverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          f F.toContourFamily t) = G)
    (hvalue :
      G - zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f =
        zetaCompletedExplicitFormulaPhi f 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 := by
  exact
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_inverseGamma_and_correction_values
      f F h hcoh G
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)
      hinverse_value
      (zetaCompletedExplicitFormulaCorrectionRightAffineKernel_integral_eq_value_ownerCorrectionAffineValues
        f F.toContourFamily h)
      hvalue

/-- Left archimedean affine line value after the correction affine value has
been discharged in its owner file.  The remaining input is the left
inverse-Gamma affine value with the resulting scalar normalization. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_of_inverseGammaLeftValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (G : ℂ)
    (hinverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily t) = G)
    (hvalue :
      G -
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
                f F.toContourFamily.c) =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_of_inverseGamma_and_correction_values
      f F h hcoh G
      (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
            f F.toContourFamily.c)
      hinverse_value
      (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_integral_eq_projectionResidue_ownerCorrectionAffineValues
        f F.toContourFamily h)
      hvalue
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 := by
  exact
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_ownerGammaBinetLineCore
      f F h hcoh

/-- Whole-line value of the left Gamma/Binet archimedean affine line. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_ownerGammaBinetLineCore
      f F h hcoh

/-- Scheduled Gamma/Binet value of the right archimedean affine line.

This is now a downstream wrapper over the scheduled coupled Gamma/Binet
full-transform owner theorem in `ArchimedeanGammaBinetLineCore`. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_scheduledFullTransform
      f F h hcoh
      (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledWindow_tendsto_phiZero_ownerGammaBinetLineCore
        f F h hcoh)

/-- Scheduled Gamma/Binet value of the left archimedean affine line.

This is now a downstream wrapper over the scheduled coupled shifted-left
Gamma/Binet full-transform owner theorem in `ArchimedeanGammaBinetLineCore`. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_scheduledFullTransform
      f F h hcoh
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledWindow_tendsto_neg_phiZero_ownerGammaBinetLineCore
        f F h hcoh)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
