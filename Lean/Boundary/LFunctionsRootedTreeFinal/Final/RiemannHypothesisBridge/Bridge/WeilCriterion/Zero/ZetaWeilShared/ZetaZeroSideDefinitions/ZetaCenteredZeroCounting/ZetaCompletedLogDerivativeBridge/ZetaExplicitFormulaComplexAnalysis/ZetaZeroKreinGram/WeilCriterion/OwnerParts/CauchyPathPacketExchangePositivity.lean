import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathPositivity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineScheduledPolynomialLimit

/-!
# Cauchy-path packet-exchange positivity

This file owns the direct positivity wrapper for the affine component
packet-exchange lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

theorem zetaCompletedAutocorrelationRightAffineKernel_integrable_of_packetExchange_owner
    (f : ZetaAdmissibleFunction)
    (rightPrimeIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (rightInverseGammaIntegrable :
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
  zetaCompletedAutocorrelationRightAffineKernel_integrable_of_component_integrable_owner
    f
    rightPrimeIntegrable
    rightInverseGammaIntegrable

theorem zetaCompletedAutocorrelationLeftAffineKernel_integrable_of_packetExchange_owner
    (f : ZetaAdmissibleFunction)
    (leftReflectedIntegrable :
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
  zetaCompletedAutocorrelationLeftAffineKernel_integrable_of_reflected_integrable_owner
    f
    leftReflectedIntegrable

theorem zetaCompletedAutocorrelationInverseGammaValue_of_packetExchange_owner
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
  zetaCompletedAutocorrelationInverseGamma_packet_value_of_difference_kernel_value_owner
    f
    differenceIntegral
    archimedeanValue

theorem zetaCompletedAutocorrelationPacketValue_of_packetExchange_owner
    (f : ZetaAdmissibleFunction)
    (rightPrimeIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (rightInverseGammaIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftReflectedIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftInverseGammaIntegrable :
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
              n t)
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
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
          (convolutionAutocorrelation f))
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
    (∫ t : ℝ,
        zetaCompletedRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) -
      ∫ t : ℝ,
        zetaCompletedLeftAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) =
      zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
          (convolutionAutocorrelation f) +
        zetaCompletedExplicitFormulaHermitianArchimedeanContribution
          (convolutionAutocorrelation f) :=
  zetaCompletedAutocorrelationAffineKernel_packet_value_of_component_values_owner
    f
    (zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
      (convolutionAutocorrelation f))
    (zetaCompletedExplicitFormulaHermitianArchimedeanContribution
      (convolutionAutocorrelation f))
    (zetaCompletedAutocorrelationAffineKernel_packet_decomposition_of_component_integrable_exchange_owner
      f
      rightPrimeIntegrable
      rightInverseGammaIntegrable
      leftReflectedIntegrable
      leftInverseGammaIntegrable
      leftArithmeticIntegralExchange)
    arithmeticEquality
    (zetaCompletedAutocorrelationInverseGammaValue_of_packetExchange_owner
      f
      differenceIntegral
      archimedeanValue)

theorem zetaCompletedAutocorrelationAffineKernel_integral_eq_physical_of_packetExchange_owner
    (f : ZetaAdmissibleFunction)
    (rightPrimeIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (rightInverseGammaIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftReflectedIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftInverseGammaIntegrable :
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
              n t)
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
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
          (convolutionAutocorrelation f))
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
    (∫ t : ℝ,
        zetaCompletedRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) -
      ∫ t : ℝ,
        zetaCompletedLeftAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) =
      explicitFormulaTwoPi *
        zetaCompletedAffinePhysicalBoundaryChannel
          (convolutionAutocorrelation f) :=
  zetaCompletedAutocorrelationAffineKernel_integral_eq_physical_of_packet_value_owner
    f
    (zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
      (convolutionAutocorrelation f))
    (zetaCompletedExplicitFormulaHermitianArchimedeanContribution
      (convolutionAutocorrelation f))
    (zetaCompletedAutocorrelationPacketValue_of_packetExchange_owner
      f
      rightPrimeIntegrable
      rightInverseGammaIntegrable
      leftReflectedIntegrable
      leftInverseGammaIntegrable
      leftArithmeticIntegralExchange
      arithmeticEquality
      differenceIntegral
      archimedeanValue)
    (zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution_div_twoPi_eq_primeContribution_autocorrelation
      f)
    (zetaCompletedAffinePhysicalBoundaryChannel_eq
      (convolutionAutocorrelation f))

def zetaCompletedAutocorrelationFamilyAnalyticPackage_of_logDerivControl
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog :
      CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
    f
    (zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
    hPhi
    hLog

theorem zetaCompletedAutocorrelationRightPrimeIntegrable_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog :
      CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  let hPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
    zetaCompletedAutocorrelationFamilyAnalyticPackage_of_logDerivControl
      f hPhi hLog
  zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrable_of_phiControl_ownerInversion
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    hPackage.phi_control

theorem zetaCompletedAutocorrelationRightPrimeIntegrable_of_phiControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrable_of_phiControl_ownerInversion
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    hPhi

theorem zetaCompletedAutocorrelationRightPrimeIntegrable_canonicalPhi_owner
    (f : ZetaAdmissibleFunction) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedAutocorrelationRightPrimeIntegrable_of_phiControl_owner
    f
    ((zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      zetaPhiAutocorrelationConcreteControl_owner) f)

theorem zetaCompletedAutocorrelationRightInverseGammaIntegrable_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog :
      CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  let hPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
    zetaCompletedAutocorrelationFamilyAnalyticPackage_of_logDerivControl
      f hPhi hLog
  zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable_of_phiControl_gammaBinet
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    hPackage.phi_control

theorem zetaCompletedAutocorrelationRightInverseGammaIntegrable_of_phiControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f)) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable_of_phiControl_gammaBinet
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    hPhi

theorem zetaCompletedAutocorrelationRightInverseGammaIntegrable_canonicalPhi_owner
    (f : ZetaAdmissibleFunction) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedAutocorrelationRightInverseGammaIntegrable_of_phiControl_owner
    f
    ((zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      zetaPhiAutocorrelationConcreteControl_owner) f)

def zetaCompletedAutocorrelationRegularFamily
    (f : ZetaAdmissibleFunction) :
    ExplicitFormulaVerticallyRegularContourFamily :=
  zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily f

def zetaCompletedAutocorrelationRegularAnalyticPackage_of_logDerivControl
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog :
      CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedAutocorrelationRegularFamily f).toContourFamily :=
  zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
    f
    (zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
    hPhi
    hLog

theorem zetaCompletedAutocorrelationLeftReflectedIntegrable_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog :
      CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_verticallyRegular
    (convolutionAutocorrelation f)
    (zetaCompletedAutocorrelationRegularFamily f)
    (zetaCompletedAutocorrelationRegularAnalyticPackage_of_logDerivControl
      f hPhi hLog)

theorem zetaCompletedAutocorrelationLeftReflectedIntegrable_of_phiControl_factorBound_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          - completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              (-t)))
        (volume : Measure ℝ))
    (hleft_bound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t)‖ ≤
          B * (1 + ‖t‖)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_phiControl_factor_bound
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    hPhi
    B
    hB_nonneg
    hfactor_meas
    hleft_bound

theorem zetaCompletedAutocorrelationLeftReflectedIntegrable_of_phiControl_gammaBinet_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  match
    zetaCompletedExplicitFormula_completedZetaNegLogDeriv_leftAffineLine_bound_of_gammaBinet
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) with
  | ⟨B, hB_nonneg, hleft_bound⟩ =>
      zetaCompletedAutocorrelationLeftReflectedIntegrable_of_phiControl_factorBound_owner
        f
        hPhi
        B
        hB_nonneg
        (zetaCompletedExplicitFormulaCompletedNegLogDeriv_reflectedRightAffineLine_aestronglyMeasurable
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        hleft_bound

theorem zetaCompletedAutocorrelationLeftReflectedIntegrable_canonicalPhi_owner
    (f : ZetaAdmissibleFunction) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedAutocorrelationLeftReflectedIntegrable_of_phiControl_gammaBinet_owner
    f
    ((zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      zetaPhiAutocorrelationConcreteControl_owner) f)

theorem zetaCompletedAutocorrelationLeftInverseGammaIntegrable_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog :
      CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  let hPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
    zetaCompletedAutocorrelationFamilyAnalyticPackage_of_logDerivControl
      f hPhi hLog
  zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_of_phiControl_gammaBinet
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    hPackage.phi_control

theorem zetaCompletedAutocorrelationLeftInverseGammaIntegrable_of_phiControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_of_phiControl_gammaBinet
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    hPhi

theorem zetaCompletedAutocorrelationLeftInverseGammaIntegrable_canonicalPhi_owner
    (f : ZetaAdmissibleFunction) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedAutocorrelationLeftInverseGammaIntegrable_of_phiControl_owner
    f
    ((zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      zetaPhiAutocorrelationConcreteControl_owner) f)

theorem zetaCompletedAutocorrelationLeftArithmeticIntegralExchange_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog :
      CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
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
            n t) :=
  zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_tsum_eq_tsum_integrals_owner
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    (zetaCompletedAutocorrelationFamilyAnalyticPackage_of_logDerivControl
      f hPhi hLog)

theorem zetaCompletedAutocorrelationArithmeticEquality_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog :
      CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
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
      zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
        (convolutionAutocorrelation f) :=
  zetaCompletedExplicitFormulaAutocorrelationCompletedAffineArithmeticIntegral_eq_twoFaceBoundary_owner
    f hPhi hLog

theorem zetaCompletedAutocorrelationInverseGammaDifferenceIntegral_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog :
      CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
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
            t) :=
  zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_sub
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    (zetaCompletedAutocorrelationFamilyAnalyticPackage_of_logDerivControl
      f hPhi hLog)

theorem zetaCompletedAutocorrelationInverseGammaDifferenceIntegral_of_componentIntegrable_owner
    (f : ZetaAdmissibleFunction)
    (rightInverseGammaIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftInverseGammaIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ)) :
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
            t) :=
  zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_sub_of_integrable
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    rightInverseGammaIntegrable
    leftInverseGammaIntegrable

theorem zetaCompletedAutocorrelationInverseGammaDifferenceIntegral_canonicalPhi_owner
    (f : ZetaAdmissibleFunction) :
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
            t) :=
  zetaCompletedAutocorrelationInverseGammaDifferenceIntegral_of_componentIntegrable_owner
    f
    (zetaCompletedAutocorrelationRightInverseGammaIntegrable_canonicalPhi_owner f)
    (zetaCompletedAutocorrelationLeftInverseGammaIntegrable_canonicalPhi_owner f)

theorem zetaCompletedAutocorrelationArchimedeanValue_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog :
      CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        t) =
      zetaCompletedExplicitFormulaHermitianArchimedeanContribution
        (convolutionAutocorrelation f) :=
  zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_archimedean_owner
    f hPhi hLog

end ZetaAdmissibleFunction

/-- Canonical scheduled Cauchy path data and the affine component packet
exchange give raw Weil positivity without using global physical
log-derivative control as an input. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetExchange_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (rightPrimeIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (rightInverseGammaIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftReflectedIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftInverseGammaIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftArithmeticIntegralExchange :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
          ∑' n : ℕ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              n t) =
          ∑' n : ℕ,
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                n t)
    (arithmeticEquality :
      ∀ f : ZetaAdmissibleFunction,
        ((∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          ∑' n : ℕ,
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                n t) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (differenceIntegral :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                t)
    (archimedeanValue :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_affineKernelIntegrableValue_owner
    K
    zetaData
    gammaData
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightAffineKernel_integrable_of_packetExchange_owner
        f
        (rightPrimeIntegrable f)
        (rightInverseGammaIntegrable f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftAffineKernel_integrable_of_packetExchange_owner
        f
        (leftReflectedIntegrable f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffineKernel_integral_eq_physical_of_packetExchange_owner
        f
        (rightPrimeIntegrable f)
        (rightInverseGammaIntegrable f)
        (leftReflectedIntegrable f)
        (leftInverseGammaIntegrable f)
        (leftArithmeticIntegralExchange f)
        (arithmeticEquality f)
        (differenceIntegral f)
        (archimedeanValue f))

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetExchange_logDerivControl_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetExchange_owner
    K
    zetaData
    gammaData
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightPrimeIntegrable_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightInverseGammaIntegrable_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftReflectedIntegrable_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftInverseGammaIntegrable_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftArithmeticIntegralExchange_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationArithmeticEquality_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationInverseGammaDifferenceIntegral_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationArchimedeanValue_of_logDerivControl_owner
        f (hPhi f) (hLog f))

end

end LFunctions
end Boundary
