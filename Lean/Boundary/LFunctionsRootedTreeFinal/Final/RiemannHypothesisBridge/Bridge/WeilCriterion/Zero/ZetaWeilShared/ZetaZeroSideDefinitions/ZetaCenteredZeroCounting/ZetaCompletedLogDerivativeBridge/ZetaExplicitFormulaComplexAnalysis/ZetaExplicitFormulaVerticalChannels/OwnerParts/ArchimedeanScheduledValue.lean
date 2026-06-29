import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ChannelRemainderAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetValue

/-!
# Scheduled archimedean affine value

This file owns the non-algebraic Gamma/Binet scheduled-window value theorem for
the archimedean right-minus-left affine kernel.  Whole-line exhaustion and
component recombination live downstream.
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

/-- Finite-window archimedean split from the pointwise identity
`archimedean = inverseGamma - correction`.

This is only Bochner integral linearity on the symmetric interval; all
integrability inputs are explicit. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_intervalIntegral_eq_inverseGamma_sub_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hinverse :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
        (volume : Measure ℝ))
    (hcorrection :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F)
        (volume : Measure ℝ))
    (T : ℝ) :
    (∫ t in Set.Icc (-T) T,
      zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t) =
      (∫ t in Set.Icc (-T) T,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) -
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t := by
  let A : ℝ → ℂ :=
    zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F
  let I : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F
  let C : ℝ → ℂ :=
    zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F
  have hsub :
      (∫ t in Set.Icc (-T) T, I t) -
          ∫ t in Set.Icc (-T) T, C t =
        ∫ t in Set.Icc (-T) T, I t - C t :=
    explicitFormulaSymmetricIntervalIntegral_sub_eq_integral_sub
      I C hinverse hcorrection T
  have hpoint :
      A = fun t : ℝ => I t - C t := by
    funext t
    exact
      zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_eq_inverseGamma_sub_correction
        f F t
  calc
    (∫ t in Set.Icc (-T) T,
      zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t) =
        ∫ t in Set.Icc (-T) T, A t := by
      exact Eq.refl _
    _ = ∫ t in Set.Icc (-T) T, I t - C t := by
      exact
        congrArg
          (fun φ : ℝ → ℂ => ∫ t in Set.Icc (-T) T, φ t)
          hpoint
    _ =
        (∫ t in Set.Icc (-T) T, I t) -
          ∫ t in Set.Icc (-T) T, C t := by
      exact hsub.symm

/-- Assembly helper for the scheduled archimedean affine value from the
inverse-Gamma scheduled value and the scheduled elementary correction value.

This theorem contains no Gamma/Binet analytic normalization.  It isolates the
final subtraction step: after the inverse-Gamma difference window has limit
`archimedean + correction`, after the correction difference window has limit
`correction`, and after the finite-window decomposition has identified the
archimedean window as inverse-Gamma minus correction, the archimedean window
has the required archimedean limit. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_scheduledWindow_tendsto_of_inverseGamma_and_correction
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hinverse :
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
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    (hcorrection :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    (hinverse_integrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ))
    (hcorrection_integrable :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  let inverseWindow : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
        f F.toContourFamily t
  let archimedeanWindow : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
        f F.toContourFamily t
  let correctionWindow : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
        f F.toContourFamily t
  have hboundary :
      zetaCompletedExplicitFormulaArchimedeanContribution f =
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) -
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
    exact
      (add_sub_cancel
        (zetaCompletedExplicitFormulaArchimedeanContribution f)
        (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)).symm
  exact
    explicitFormulaScheduledComponent_tendsto_of_eq_total_sub_remainder
      inverseWindow
      archimedeanWindow
      correctionWindow
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      (zetaCompletedExplicitFormulaArchimedeanContribution f)
        (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      hboundary
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_intervalIntegral_eq_inverseGamma_sub_correction
          f F.toContourFamily hinverse_integrable hcorrection_integrable
          ((F.toContourFamily.rectangle (h.height_schedule.height u)).T))
      hinverse
      hcorrection

/-- Owner analytic leaf: scheduled-window value theorem for the archimedean
right-minus-left affine kernel.

This is the Binet/Stirling normalization theorem for the archimedean component
alone.  It should be proved from the Gamma/Binet expansion on the paired
vertical lines, the Paley-Wiener decay of `Φ_f`, and the archimedean contour
normalization.  It must not be derived from combined inverse-Gamma
normalization, which consumes the archimedean component value. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_scheduledWindow_tendsto_archimedeanContribution_ownerScheduledValue
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
  sorry

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
