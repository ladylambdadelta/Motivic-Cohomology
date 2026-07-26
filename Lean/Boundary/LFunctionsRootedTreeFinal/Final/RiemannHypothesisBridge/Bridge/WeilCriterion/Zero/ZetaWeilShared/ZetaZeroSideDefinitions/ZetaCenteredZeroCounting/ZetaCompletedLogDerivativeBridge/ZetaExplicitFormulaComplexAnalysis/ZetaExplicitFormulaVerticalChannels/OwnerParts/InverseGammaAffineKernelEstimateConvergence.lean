import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimateIntegrability
/-!
# Inverse-Gamma affine-kernel estimate split part

This file is a mechanical owner split of the inverse-Gamma affine-kernel estimate.
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

/-- Symmetric-window convergence of the inverse-Gamma difference affine kernel
to its actual whole-line integral under the regular Gamma/Binet hypotheses.
This separates exhaustion from the later value identification with the
archimedean plus correction boundary terms. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_symmetric_of_gammaBinet_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) := by
  exact
    explicitFormulaSymmetricIntervalIntegral_tendsto_integral
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_gammaBinet_regular
        f F h hregular)

/-- Rectangle-window convergence of the inverse-Gamma difference affine kernel
to its actual whole-line integral under the regular Gamma/Binet hypotheses. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_unscheduled_of_gammaBinet_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) := by
  exact
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      (zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_symmetric_of_gammaBinet_regular
        f F h hregular)

/-- Scheduled-window convergence of the inverse-Gamma difference affine kernel
to its actual whole-line integral under the regular Gamma/Binet hypotheses. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_of_gammaBinet_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t
  have hkernel :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_unscheduled_of_gammaBinet_regular
      f F h hregular
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      hkernel
      h.height_schedule.cofinal

/-- Symmetric-window inverse-Gamma completion convergence from the regular
Gamma/Binet majorant hypotheses and a separately proved whole-line value
identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_symmetric_of_gammaBinet_regular_and_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
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
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  exact
    explicitFormulaSymmetricIntervalIntegral_tendsto_value
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_gammaBinet_regular
        f F h hregular)
      hvalue

/-- Rectangle-window inverse-Gamma completion convergence from the regular
Gamma/Binet majorant hypotheses and a separately proved whole-line value
identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_unscheduled_of_gammaBinet_regular_and_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
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
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  exact
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      (zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_symmetric_of_gammaBinet_regular_and_integral_eq
        f F h hregular hvalue)

/-- Scheduled-window inverse-Gamma completion convergence from the regular
Gamma/Binet majorant hypotheses and a separately proved whole-line value
identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_of_gammaBinet_regular_and_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
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
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t
  have hkernel :
      Tendsto K atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_unscheduled_of_gammaBinet_regular_and_integral_eq
      f F h hregular hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      hkernel
      h.height_schedule.cofinal

/-- The whole-line inverse-Gamma difference affine-kernel value follows from a
scheduled inverse-Gamma completion value theorem.  This is a compatibility
transport; the owner normalization is the whole-line Gamma/Binet value. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_scheduled_tendsto_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
      zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
  have hintegral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
        atTop
        (𝓝
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_of_gammaBinet_regular
      f F h hregular
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      hintegral
      hscheduled

/-- Vertically regular whole-line inverse-Gamma value from a scheduled
inverse-Gamma completion value theorem.  This theorem is retained as a transport
wrapper; the owner normalization is the whole-line Gamma/Binet value. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_verticallyRegular_scheduled_tendsto
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hscheduled :
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
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f :=
  zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_scheduled_tendsto_archimedean_add_correction
    f F.toContourFamily h
    (zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F)
    hscheduled

/-- On a finite symmetric window, the inverse-Gamma difference affine kernel
recombines into the archimedean and elementary correction difference kernels. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_intervalIntegral_eq_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (∫ t in Set.Icc (-T) T,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
      ∫ t in Set.Icc (-T) T,
        zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t +
          zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t := by
  exact MeasureTheory.setIntegral_congr_fun
    measurableSet_Icc
    (fun t _ht =>
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_eq_archimedean_add_correction
        f F t)

/-- Whole-line additive splitting of the inverse-Gamma difference affine kernel.

This lemma contains only integration algebra.  The analytic normalization still
lives in the owner normalization theorem: this helper may be used only after
the archimedean and elementary correction summands have independently supplied
their own integrability and value statements. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_integral_add_correction_integral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (harch :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F)
        (volume : Measure ℝ))
    (hcorr :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F)
        (volume : Measure ℝ)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t := by
  have hpoint :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t +
            zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_eq_archimedean_add_correction
          f F t)
  exact Eq.trans
    (integral_congr_ae hpoint)
    (integral_add harch hcorr)

/-- Whole-line splitting of the right-minus-left inverse-Gamma affine kernel
into its two affine-line components.

This is only Bochner-integral algebra.  It is the component-level counterpart
of the archimedean/correction split above and is useful when a later proof has
an independent right inverse-Gamma value and the already normalized
right-minus-left inverse-Gamma value. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_rightIntegral_sub_leftIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hright :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
        (volume : Measure ℝ))
    (hleft :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume : Measure ℝ)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
  exact integral_sub hright hleft

/-- Extract the left inverse-Gamma affine value from a right affine value and
the right-minus-left difference value.

The equation is intentionally algebraic: since the difference kernel is
`right - left`, a proved value for the difference and a proved value for the
right component determine the left component as `right - difference`. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_rightValue_sub_differenceValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hright :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
        (volume : Measure ℝ))
    (hleft :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume : Measure ℝ))
    (R D : ℂ)
    (hright_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) = R)
    (hdifference_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) = D) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) =
      R - D := by
  let L : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  have hsplit :
      D = R - L := by
    calc
      D =
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t := by
        exact hdifference_value.symm
      _ =
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
        exact
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_rightIntegral_sub_leftIntegral
            f F hright hleft
      _ = R - L := by
        exact congrArg
          (fun z : ℂ => z - L)
          hright_value
  have hR_sub_D :
      R - D = L := by
    calc
      R - D = R - (R - L) := by
        exact congrArg (fun z : ℂ => R - z) hsplit
      _ = L := by
        exact sub_sub_cancel R L
  exact hR_sub_D.symm

/-- Integrability of the right-minus-left inverse-Gamma affine kernel under the
regular Gamma/Binet hypotheses. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (volume : Measure ℝ) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_gammaBinet_regular
      f F h hregular

/-- Scheduled inverse-Gamma completion convergence once the whole-line
inverse-Gamma value identity has been proved. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernelIntegral_tendsto_archimedean_add_correction_direct
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
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
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_of_gammaBinet_regular_and_integral_eq
      f F h hregular hvalue

/-- Whole-line value of the right-minus-left inverse-Gamma affine kernel from a
separately proved scheduled inverse-Gamma normalization. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
      zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
  exact
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_scheduled_tendsto_archimedean_add_correction
      f F h hregular hscheduled

/-- Symmetric-window inverse-Gamma completion convergence on vertical lines from
the whole-line inverse-Gamma value identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_symmetric
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun T : ℝ =>
        (∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
          ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let K : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F
  let R : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F
  let L : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F
  have hK_limit :
      Tendsto
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, K t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_symmetric_of_gammaBinet_regular_and_integral_eq
      f F h hregular hvalue
  have hR_integrable :
      Integrable R (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable f F
      h
  have hL_integrable :
      Integrable L (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable f F
      h hregular
  have hdisplay :
      (fun T : ℝ =>
        (∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
          ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) =
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, K t) := by
    funext T
    exact
      explicitFormulaSymmetricIntervalIntegral_sub_eq_integral_sub
        R L hR_integrable hL_integrable T
  exact Eq.subst
    (motive := fun ψ : ℝ → ℂ =>
      Tendsto ψ atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    hdisplay.symm
    hK_limit

/-- Unscheduled rectangle-window inverse-Gamma completion convergence on
vertical lines from the whole-line inverse-Gamma value identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_unscheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun T : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
          ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let R : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc (-T) T,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t
  let L : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc (-T) T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  let Rrect : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t
  let Lrect : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  have hR : Rrect = R := by
    funext T
    exact
      explicitFormulaRectangleWindowIntegral_eq_symmetric
        F
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
        T
  have hL : Lrect = L := by
    funext T
    exact
      explicitFormulaRectangleWindowIntegral_eq_symmetric
        F
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        T
  have hdiff :
      (fun T : ℝ => Rrect T - Lrect T) =
        fun T : ℝ => R T - L T := by
    funext T
    exact congrArg₂ HSub.hSub (congrArg (fun φ : ℝ → ℂ => φ T) hR)
      (congrArg (fun φ : ℝ → ℂ => φ T) hL)
  exact Eq.subst
    (motive := fun ψ : ℝ → ℂ =>
      Tendsto ψ atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    hdiff.symm
    (zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_symmetric
      f F h hregular hvalue)

/-- Kernel-level inverse-Gamma completion convergence on the scheduled vertical
lines from the whole-line inverse-Gamma value identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
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
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    (∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
      ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  have hkernel :
      Tendsto K atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_unscheduled
      f F h hregular hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      hkernel
      h.height_schedule.cofinal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
