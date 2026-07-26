import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanScheduledChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionVerticalConvergence
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightOnePoleOffPoleDecayEstimate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport

/-!
# Archimedean vertical analytic estimates

This file owns the analytic estimates behind archimedean vertical-channel
transport: inverse-Gamma completion convergence and correction-channel
convergence from their owner-level analytic leaves.
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

/-- The scheduled correction-channel estimate supplied by the pole-face
correction transport theorem, once the right one-pole projection limit has
been proved. -/
theorem zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel_tendsto_correctionContribution_of_rightOnePoleProjection
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
          f F h u)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_concrete_ownerChannelTransportAnalytic
      f F h hone

/-- Conditional archimedean scheduled estimates from the inverse-Gamma estimate
and the independently supplied right one-pole projection limit. -/
theorem zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_inverseGamma_and_rightOnePoleProjection
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hinverse :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
            f F h u)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :
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
  And.intro hinverse
    (zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel_tendsto_correctionContribution_of_rightOnePoleProjection
      f F h hone)

/-- Scheduled right one-pole projection limit needed by correction-channel
convergence. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledVerticalIntegral_tendsto_projection
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleOffPoleVerticalIntegral_tendsto_projection
      f F h

/-- The scheduled inverse-Gamma completion channel converges by the named
kernel-level inverse-Gamma estimate. -/
theorem zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
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
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let K : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
      ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  have hkernel :
      Tendsto K atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction
      f F h hregular hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel f F h u)
      K
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      hkernel
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_eq_affineKernelIntegrals
          f F h u)

/-- The scheduled inverse-Gamma completion channel converges under the honest
regular Gamma/Binet hypotheses once the whole-line inverse-Gamma value identity
has been proved separately. -/
theorem zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_archimedean_add_correction_of_gammaBinetCoherence_regular_and_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
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
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let K : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
      ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  have hR_integrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
        (volume : Measure ℝ) :=
    (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinet
      f F h).integrable
  have hL_integrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume : Measure ℝ) :=
    (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinet
      f F h hregular).integrable
  have hdiff :
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
      K := by
    funext u
    let T : ℝ := (F.rectangle (h.height_schedule.height u)).T
    let R : ℝ → ℂ :=
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F
    let L : ℝ → ℂ :=
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F
    have hsub :
        (∫ t in Set.Icc (-T) T, R t) -
            ∫ t in Set.Icc (-T) T, L t =
          ∫ t in Set.Icc (-T) T, R t - L t :=
      explicitFormulaSymmetricIntervalIntegral_sub_eq_integral_sub
        R L hR_integrable hL_integrable T
    have hkernel :
        (fun t : ℝ => R t - L t) =
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F := by
      funext t
      exact Eq.refl _
    have hsub_kernel :
        (∫ t in Set.Icc (-T) T, R t) -
            ∫ t in Set.Icc (-T) T, L t =
          ∫ t in Set.Icc (-T) T,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t :=
      Eq.subst
        (motive := fun φ : ℝ → ℂ =>
          (∫ t in Set.Icc (-T) T, R t) -
              ∫ t in Set.Icc (-T) T, L t =
            ∫ t in Set.Icc (-T) T, φ t)
        hkernel
        hsub
    exact hsub_kernel.symm
  have hkernel_difference :
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
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_of_gammaBinet_regular_and_integral_eq
      f F h hregular hvalue
  have hkernel :
      Tendsto K atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop
          (𝓝
            (zetaCompletedExplicitFormulaArchimedeanContribution f +
              zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
      hdiff
      hkernel_difference
  exact
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel f F h u)
      K
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      hkernel
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_eq_affineKernelIntegrals
          f F h u)

/-- Vertically regular version of the scheduled inverse-Gamma completion
convergence theorem.  The regularity proof is supplied by the contour owner;
the only analytic input retained here is the whole-line inverse-Gamma value
identity. -/
theorem zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_archimedean_add_correction_of_verticallyRegular_gammaBinet_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
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
  zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_archimedean_add_correction_of_gammaBinetCoherence_regular_and_integral_eq
    f F.toContourFamily h
    (zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F)
    hcoh hvalue

/-- Conditional scheduled inverse-Gamma completion convergence to the
whole-line inverse-Gamma difference integral for a vertically regular contour
family, using the regular left-line Gamma estimate and the Binet principal-log
coherence package.  Identifying this integral with the archimedean plus
correction contribution remains the separate value theorem. -/
theorem zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_integral_of_gammaBinetCoherence
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
          f F.toContourFamily h u)
      atTop
      (𝓝
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
            f F.toContourFamily t)) := by
  let K : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        f F.toContourFamily t) -
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
        f F.toContourFamily t
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hintegrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_gammaBinet_regular
      f F.toContourFamily h hregular
  have hkernel :
      Tendsto K atTop
        (𝓝
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
              f F.toContourFamily t)) := by
    have hright :
        Integrable
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinet
        f F.toContourFamily h).integrable
    have hleft :
        Integrable
          (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinet
        f F.toContourFamily h hregular).integrable
    have hdiff :
        Tendsto
          (fun T : ℝ =>
            (∫ t in Set.Icc (-T) T,
              zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
                f F.toContourFamily t) -
              ∫ t in Set.Icc (-T) T,
                zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
                  f F.toContourFamily t)
          atTop
          (𝓝
            (∫ t : ℝ,
              zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
                f F.toContourFamily t)) :=
      zetaCompletedExplicitFormulaSymmetricIntegral_sub_tendsto_integral_sub
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          f F.toContourFamily)
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily)
        hright hleft
    exact hdiff.comp h.height_schedule.cofinal
  exact
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
          f F.toContourFamily h u)
      K
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t)
      hkernel
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_eq_affineKernelIntegrals
          f F.toContourFamily h u)

/-- Combined archimedean scheduled analytic estimates. -/
theorem zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
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
    (zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_archimedean_add_correction
      f F h hregular hcoh hvalue)
    (zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledVerticalIntegral_tendsto_projection
      f F h)

/-- Combined archimedean scheduled analytic estimates for a vertically regular
contour family, exposing the inverse-Gamma whole-line value identity as the
remaining archimedean analytic input. -/
theorem zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_verticallyRegular_gammaBinet_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
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
  zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_inverseGamma_and_rightOnePoleProjection
    f F.toContourFamily h
    (zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_archimedean_add_correction_of_verticallyRegular_gammaBinet_integral_eq
      f F h hcoh hvalue)
    (zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledVerticalIntegral_tendsto_projection
      f F.toContourFamily h)

/-- The scheduled correction channel converges to the standard correction
contribution. -/
theorem zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel_tendsto_correctionContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
          f F h u)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
  zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel_tendsto_correctionContribution_of_rightOnePoleProjection
    f F h
    (zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledVerticalIntegral_tendsto_projection
      f F h)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
