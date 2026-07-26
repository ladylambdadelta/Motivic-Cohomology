import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineScheduledPhysicalLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.ScheduledPolynomialGrowth

/-!
# Scheduled-polynomial completed affine physical limits

This file owns the schedule-only part of the completed affine physical limit for
fixed-degree scheduled packages.  The analytic work is deliberately exposed as
the three lower sinks: right affine integrability, left affine integrability,
and the full-line completed affine value.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

theorem zetaCompletedAutocorrelationRightAffineKernel_integrable_of_component_integrable_owner
    (f : ZetaAdmissibleFunction)
    (primeIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (inverseGammaIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ)) :
    Integrable
      (zetaCompletedRightAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedRightAffineKernel_integrable_of_component_integrable_owner
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    primeIntegrable
    inverseGammaIntegrable

theorem zetaCompletedAutocorrelationLeftAffineKernel_integrable_of_reflected_integrable_owner
    (f : ZetaAdmissibleFunction)
    (reflectedIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ)) :
    Integrable
      (zetaCompletedLeftAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedLeftAffineKernel_integrable_of_reflected_integrable_owner
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    reflectedIntegrable

theorem zetaCompletedAutocorrelationAffineKernel_integral_eq_physical_of_packet_value_owner
    (f : ZetaAdmissibleFunction)
    (arithmeticValue archimedeanValue : ℂ)
    (packetValue :
      (∫ t : ℝ,
          zetaCompletedRightAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) -
        (∫ t : ℝ,
          zetaCompletedLeftAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
        arithmeticValue + archimedeanValue)
    (arithmeticDivision :
      arithmeticValue / explicitFormulaTwoPi =
        zetaCompletedExplicitFormulaPrimeContribution
          (convolutionAutocorrelation f))
    (boundaryEquality :
      zetaCompletedAffinePhysicalBoundaryChannel
          (convolutionAutocorrelation f) =
        zetaCompletedExplicitFormulaPrimeContribution
            (convolutionAutocorrelation f) +
          archimedeanValue / explicitFormulaTwoPi) :
    (∫ t : ℝ,
        zetaCompletedRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) -
      (∫ t : ℝ,
        zetaCompletedLeftAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) =
        explicitFormulaTwoPi *
          zetaCompletedAffinePhysicalBoundaryChannel
            (convolutionAutocorrelation f) :=
  zetaCompletedAffineKernelIntegral_eq_physical_of_packet_value_owner
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    arithmeticValue
    archimedeanValue
    packetValue
    arithmeticDivision
    boundaryEquality

theorem zetaCompletedAutocorrelationAffineKernel_packet_value_of_component_values_owner
    (f : ZetaAdmissibleFunction)
    (arithmeticValue archimedeanValue : ℂ)
    (packetDecomposition :
      (∫ t : ℝ,
          zetaCompletedRightAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) -
        (∫ t : ℝ,
          zetaCompletedLeftAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
        ((∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
              (convolutionAutocorrelation f)
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          ∑' n : ℕ,
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                (convolutionAutocorrelation f)
                (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                n t) +
        ((∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
              (convolutionAutocorrelation f)
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              (convolutionAutocorrelation f)
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t))
    (arithmeticEquality :
      ((∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) -
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              (convolutionAutocorrelation f)
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              n t) =
        arithmeticValue)
    (inverseGammaEquality :
      ((∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) -
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
        archimedeanValue)) :
    (∫ t : ℝ,
        zetaCompletedRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) -
      (∫ t : ℝ,
        zetaCompletedLeftAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) =
      arithmeticValue + archimedeanValue :=
  zetaCompletedAffineKernel_packet_value_of_component_values_owner
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    arithmeticValue
    archimedeanValue
    packetDecomposition
    arithmeticEquality
    inverseGammaEquality

theorem zetaCompletedAutocorrelationInverseGamma_packet_value_of_difference_kernel_value_owner
    (f : ZetaAdmissibleFunction)
    (differenceIntegral :
      (∫ t : ℝ,
        zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              (convolutionAutocorrelation f)
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t)
    (archimedeanValue :
      (∫ t : ℝ,
        zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) =
        zetaCompletedExplicitFormulaHermitianArchimedeanContribution
          (convolutionAutocorrelation f)) :
    ((∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) -
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) =
      zetaCompletedExplicitFormulaHermitianArchimedeanContribution
        (convolutionAutocorrelation f) :=
  zetaCompletedAffineInverseGamma_packet_value_of_difference_kernel_value_owner
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    differenceIntegral
    archimedeanValue

theorem zetaCompletedAffineKernel_packet_decomposition_of_component_integrable_exchange_owner
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (rightArithmeticIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          probe family)
        (volume : Measure ℝ))
    (rightGammaIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          probe family)
        (volume : Measure ℝ))
    (reflectedCompletedIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          probe family)
        (volume : Measure ℝ))
    (leftGammaIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          probe family)
        (volume : Measure ℝ))
    (leftArithmeticIntegralExchange :
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            probe family n t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              probe family n t) :
    (∫ t : ℝ,
        zetaCompletedRightAffineKernel probe family t) -
      ∫ t : ℝ,
        zetaCompletedLeftAffineKernel probe family t =
      ((∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            probe family t) -
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              probe family n t) +
      ((∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            probe family t) -
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            probe family t) :=
  let rightArithmetic : ℝ → ℂ :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
      probe family
  let rightGamma : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
      probe family
  let leftArithmetic : ℝ → ℂ := fun t : ℝ =>
    ∑' n : ℕ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
        probe family n t
  let leftGamma : ℝ → ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
      probe family
  let leftArithmeticEquality :
      leftArithmetic =
        fun t : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
              probe family t -
            leftGamma t :=
    funext
      (fun t : ℝ =>
        let decomposition :=
          zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_eq_tsum_termKernel_add_reflectedInverseGamma_ownerSummable
            probe family t
        Eq.trans
          (add_sub_cancel_right
            (leftArithmetic t)
            (leftGamma t)).symm
          (congrArg
            (fun value : ℂ => value - leftGamma t)
            decomposition.symm))
  let leftArithmeticIntegrable :
      Integrable leftArithmetic (volume : Measure ℝ) :=
    Eq.subst
      (motive := fun kernel : ℝ → ℂ =>
        Integrable kernel (volume : Measure ℝ))
      leftArithmeticEquality.symm
      (reflectedCompletedIntegrable.sub leftGammaIntegrable)
  let rightIntegralEquality :
      (∫ t : ℝ,
        zetaCompletedRightAffineKernel probe family t) =
        (∫ t : ℝ, rightArithmetic t) +
          ∫ t : ℝ, rightGamma t :=
    let pointEquality :
        zetaCompletedRightAffineKernel probe family =
          fun t : ℝ => rightArithmetic t + rightGamma t :=
      funext
        (fun t : ℝ =>
          zetaCompletedExplicitFormula_completedRightAffineKernel_eq_prime_add_inverseGamma
            probe family t)
    Eq.trans
      (congrArg (fun kernel : ℝ → ℂ => ∫ t : ℝ, kernel t) pointEquality)
      (integral_add rightArithmeticIntegrable rightGammaIntegrable)
  let leftKernelEquality :
      zetaCompletedLeftAffineKernel probe family =
        fun t : ℝ => leftArithmetic t + leftGamma t :=
    funext
      (fun t : ℝ =>
        let reflection :
            completedZetaNegLogDeriv
                (zetaCompletedExplicitFormulaLeftAffineLine
                  family t) =
              -completedZetaNegLogDeriv
                (zetaCompletedExplicitFormulaRightAffineLine
                  family (-t)) :=
          zetaCompletedExplicitFormula_completedZetaNegLogDeriv_leftAffineLine_eq_neg_rightAffineLine
            family t
        let leftToReflected :
            zetaCompletedLeftAffineKernel probe family t =
              zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
                probe family t :=
          congrArg
            (fun factor : ℂ =>
              factor *
                zetaCompletedExplicitFormulaPhi probe
                  (zetaCompletedExplicitFormulaLeftCenteredAffineLine
                    family t))
            reflection
        let reflectedDecomposition :=
          zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_eq_tsum_termKernel_add_reflectedInverseGamma_ownerSummable
            probe family t
        Eq.trans leftToReflected reflectedDecomposition)
  let leftIntegralEquality :
      (∫ t : ℝ,
        zetaCompletedLeftAffineKernel probe family t) =
        (∫ t : ℝ, leftArithmetic t) +
          ∫ t : ℝ, leftGamma t :=
    Eq.trans
      (congrArg (fun kernel : ℝ → ℂ => ∫ t : ℝ, kernel t) leftKernelEquality)
      (integral_add leftArithmeticIntegrable leftGammaIntegrable)
  let regrouped :
      ((∫ t : ℝ, rightArithmetic t) + ∫ t : ℝ, rightGamma t) -
          ((∫ t : ℝ, leftArithmetic t) + ∫ t : ℝ, leftGamma t) =
        ((∫ t : ℝ, rightArithmetic t) - ∫ t : ℝ, leftArithmetic t) +
          ((∫ t : ℝ, rightGamma t) - ∫ t : ℝ, leftGamma t) :=
    completedAffinePacket_sub_packet_eq_coordinate_sub_add_coordinate_sub
      (∫ t : ℝ, rightArithmetic t)
      (∫ t : ℝ, rightGamma t)
      (∫ t : ℝ, leftArithmetic t)
      (∫ t : ℝ, leftGamma t)
  let exchanged :
      ((∫ t : ℝ, rightArithmetic t) - ∫ t : ℝ, leftArithmetic t) +
          ((∫ t : ℝ, rightGamma t) - ∫ t : ℝ, leftGamma t) =
        ((∫ t : ℝ, rightArithmetic t) -
          ∑' n : ℕ,
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                probe family n t) +
          ((∫ t : ℝ, rightGamma t) - ∫ t : ℝ, leftGamma t) :=
    congrArg
      (fun arithmeticValue : ℂ =>
        arithmeticValue +
          ((∫ t : ℝ, rightGamma t) - ∫ t : ℝ, leftGamma t))
      (congrArg
        (fun leftValue : ℂ =>
          (∫ t : ℝ, rightArithmetic t) - leftValue)
        leftArithmeticIntegralExchange)
  Eq.trans
    (congrArg₂ HSub.hSub rightIntegralEquality leftIntegralEquality)
    (Eq.trans regrouped exchanged)

theorem zetaCompletedAutocorrelationAffineKernel_packet_decomposition_of_component_integrable_exchange_owner
    (f : ZetaAdmissibleFunction)
    (rightArithmeticIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (rightGammaIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (reflectedCompletedIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftGammaIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftArithmeticIntegralExchange :
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            n t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              (convolutionAutocorrelation f)
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              n t) :
    (∫ t : ℝ,
        zetaCompletedRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) -
      (∫ t : ℝ,
        zetaCompletedLeftAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) =
      ((∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) -
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              (convolutionAutocorrelation f)
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              n t) +
      ((∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) -
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) :=
  zetaCompletedAffineKernel_packet_decomposition_of_component_integrable_exchange_owner
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    rightArithmeticIntegrable
    rightGammaIntegrable
    reflectedCompletedIntegrable
    leftGammaIntegrable
    leftArithmeticIntegralExchange

theorem zetaCompletedPolynomialScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (h :
      ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage probe family)
    (rightIntegrable :
      Integrable
        (zetaCompletedRightAffineKernel probe family)
        (volume : Measure ℝ))
    (leftIntegrable :
      Integrable
        (zetaCompletedLeftAffineKernel probe family)
        (volume : Measure ℝ))
    (valueEquality :
      (∫ t : ℝ,
          zetaCompletedRightAffineKernel probe family t) -
        (∫ t : ℝ,
          zetaCompletedLeftAffineKernel probe family t) =
          explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel probe) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedAffineVerticalChannel
          probe family (h.height_schedule.height u))
      atTop
      (𝓝
        (explicitFormulaTwoPi *
          zetaCompletedAffinePhysicalBoundaryChannel probe)) :=
  zetaCompletedScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
    probe
    family
    h.height_schedule
    rightIntegrable
    leftIntegrable
    valueEquality

theorem zetaCompletedAutocorrelationPolynomialScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
    (f : ZetaAdmissibleFunction)
    (h :
      ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (rightIntegrable :
      Integrable
        (zetaCompletedRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftIntegrable :
      Integrable
        (zetaCompletedLeftAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (valueEquality :
      (∫ t : ℝ,
          zetaCompletedRightAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) -
        (∫ t : ℝ,
          zetaCompletedLeftAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
          explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel
              (convolutionAutocorrelation f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedAffineVerticalChannel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          (h.height_schedule.height u))
      atTop
      (𝓝
        (explicitFormulaTwoPi *
          zetaCompletedAffinePhysicalBoundaryChannel
            (convolutionAutocorrelation f))) :=
  zetaCompletedPolynomialScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    h
    rightIntegrable
    leftIntegrable
    valueEquality

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
