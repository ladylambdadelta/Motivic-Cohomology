import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathPacketExchangePositivity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineRegularAnalyticTransport

/-!
# Analytic-package affine packet facts

This owner part exposes the vertical affine packet facts that only require an
explicit analytic package.  The archimedean transport value remains separate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

structure ZetaCompletedAutocorrelationAffinePacketData
    (f : ZetaAdmissibleFunction) where
  right_prime_integrable :
    Integrable
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ)
  right_inverse_gamma_integrable :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ)
  left_reflected_integrable :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ)
  left_inverse_gamma_integrable :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ)
  left_arithmetic_integral_exchange :
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
            n t
  arithmetic_equality :
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
        (convolutionAutocorrelation f)
  inverse_gamma_difference_integral :
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
            t
  archimedean_value :
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        t) =
      zetaCompletedExplicitFormulaHermitianArchimedeanContribution
        (convolutionAutocorrelation f)

def ZetaCompletedAutocorrelationAffinePacketData.of_componentFacts
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
    (inverseGammaDifferenceIntegral :
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
    ZetaCompletedAutocorrelationAffinePacketData f :=
  { right_prime_integrable := rightPrimeIntegrable
    right_inverse_gamma_integrable := rightInverseGammaIntegrable
    left_reflected_integrable := leftReflectedIntegrable
    left_inverse_gamma_integrable := leftInverseGammaIntegrable
    left_arithmetic_integral_exchange := leftArithmeticIntegralExchange
    arithmetic_equality := arithmeticEquality
    inverse_gamma_difference_integral := inverseGammaDifferenceIntegral
    archimedean_value := archimedeanValue }

theorem zetaCompletedAutocorrelationAffinePacketData_of_componentFacts_owner
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
    (inverseGammaDifferenceIntegral :
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
    ZetaCompletedAutocorrelationAffinePacketData f :=
  ZetaCompletedAutocorrelationAffinePacketData.of_componentFacts
    f
    rightPrimeIntegrable
    rightInverseGammaIntegrable
    leftReflectedIntegrable
    leftInverseGammaIntegrable
    leftArithmeticIntegralExchange
    arithmeticEquality
    inverseGammaDifferenceIntegral
    archimedeanValue

theorem zetaCompletedAutocorrelationRightPrimeIntegrable_of_analyticPackage_owner
    (f : ZetaAdmissibleFunction)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrable_of_phiControl_ownerInversion
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    analyticPackage.phi_control

theorem zetaCompletedAutocorrelationRightInverseGammaIntegrable_of_analyticPackage_owner
    (f : ZetaAdmissibleFunction)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable_of_phiControl_gammaBinet
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    analyticPackage.phi_control

theorem zetaCompletedAutocorrelationLeftReflectedIntegrable_of_regularAnalyticPackage_owner
    (f : ZetaAdmissibleFunction)
    (regularAnalyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedAutocorrelationRegularFamily f).toContourFamily) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedAutocorrelationLeftReflectedIntegrable_of_phiControl_gammaBinet_owner
    f
    regularAnalyticPackage.phi_control

theorem zetaCompletedAutocorrelationLeftInverseGammaIntegrable_of_analyticPackage_owner
    (f : ZetaAdmissibleFunction)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_of_phiControl_gammaBinet
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    analyticPackage.phi_control

theorem zetaCompletedAutocorrelationLeftArithmeticIntegralExchange_of_analyticPackage_owner
    (f : ZetaAdmissibleFunction)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
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
    analyticPackage

theorem zetaCompletedAutocorrelationLeftArithmeticIntegralExchange_of_phiControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f)) :
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
  zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_tsum_eq_tsum_integrals_of_phiControl_owner
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    hPhi

theorem zetaCompletedAutocorrelationLeftArithmeticIntegralExchange_canonicalPhi_owner
    (f : ZetaAdmissibleFunction) :
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
  zetaCompletedAutocorrelationLeftArithmeticIntegralExchange_of_phiControl_owner
    f
    ((zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      zetaPhiAutocorrelationConcreteControl_owner) f)

theorem zetaCompletedAutocorrelationArithmeticEquality_of_analyticPackage_owner
    (f : ZetaAdmissibleFunction)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
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
  zetaCompletedExplicitFormulaCompletedAffineArithmeticIntegral_eq_twoFaceBoundary_of_analyticPackage_owner
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    analyticPackage

theorem zetaCompletedAutocorrelationArithmeticEquality_of_phiControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f)) :
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
  let rightValue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution
          (convolutionAutocorrelation f) :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integral_eq_primeNaturalOneSidedContribution_of_phiControl_ownerInversion
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
      hPhi
  zetaCompletedExplicitFormulaCompletedAffineArithmeticIntegral_eq_twoFaceBoundary_of_rightValue_owner
    (convolutionAutocorrelation f)
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    rightValue

theorem zetaCompletedAutocorrelationArithmeticEquality_canonicalPhi_owner
    (f : ZetaAdmissibleFunction) :
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
  zetaCompletedAutocorrelationArithmeticEquality_of_phiControl_owner
    f
    ((zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      zetaPhiAutocorrelationConcreteControl_owner) f)

theorem zetaCompletedAutocorrelationInverseGammaDifferenceIntegral_of_analyticPackage_owner
    (f : ZetaAdmissibleFunction)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
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
    analyticPackage

theorem zetaCompletedAutocorrelationArchimedeanValue_of_inverseGammaTransport_owner
    (f : ZetaAdmissibleFunction)
    (transport :
      (∫ t : ℝ,
        zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) =
        ∫ t : ℝ,
          zetaCompletedHermitianInverseGammaIntegrand
            (convolutionAutocorrelation f) t) :
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        t) =
      zetaCompletedExplicitFormulaHermitianArchimedeanContribution
        (convolutionAutocorrelation f) :=
  Eq.trans
    transport
    (zetaCompletedHermitianInverseGammaIntegrand_integral_eq_archimedeanContribution
      (convolutionAutocorrelation f))

theorem zetaCompletedAutocorrelationInverseGammaTransport_of_analyticPackage_owner
    (f : ZetaAdmissibleFunction)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        t) =
      ∫ t : ℝ,
        zetaCompletedHermitianInverseGammaIntegrand
          (convolutionAutocorrelation f) t :=
  zetaCompletedAffineRegularInverseGamma_integral_eq_critical_of_analyticPackage_owner
    f analyticPackage

theorem zetaCompletedAutocorrelationInverseGammaTransport_of_phiControl_gammaBinet_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f)) :
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        t) =
      ∫ t : ℝ,
        zetaCompletedHermitianInverseGammaIntegrand
          (convolutionAutocorrelation f) t :=
  zetaCompletedAffineRegularInverseGamma_integral_eq_critical_of_phiControl_gammaBinet_owner
    f hPhi

theorem zetaCompletedAutocorrelationArchimedeanValue_of_phiControl_gammaBinet_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f)) :
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        t) =
      zetaCompletedExplicitFormulaHermitianArchimedeanContribution
        (convolutionAutocorrelation f) :=
  zetaCompletedAutocorrelationArchimedeanValue_of_inverseGammaTransport_owner
    f
    (zetaCompletedAutocorrelationInverseGammaTransport_of_phiControl_gammaBinet_owner
      f hPhi)

theorem zetaCompletedAutocorrelationArchimedeanValue_canonicalPhi_owner
    (f : ZetaAdmissibleFunction) :
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        t) =
      zetaCompletedExplicitFormulaHermitianArchimedeanContribution
        (convolutionAutocorrelation f) :=
  zetaCompletedAutocorrelationArchimedeanValue_of_phiControl_gammaBinet_owner
    f
    ((zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      zetaPhiAutocorrelationConcreteControl_owner) f)

def ZetaCompletedAutocorrelationAffinePacketData.of_analyticPackage
    (f : ZetaAdmissibleFunction)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (regularAnalyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedAutocorrelationRegularFamily f).toContourFamily) :
    ZetaCompletedAutocorrelationAffinePacketData f :=
  zetaCompletedAutocorrelationAffinePacketData_of_componentFacts_owner
    f
    (zetaCompletedAutocorrelationRightPrimeIntegrable_of_analyticPackage_owner
      f analyticPackage)
    (zetaCompletedAutocorrelationRightInverseGammaIntegrable_of_analyticPackage_owner
      f analyticPackage)
    (zetaCompletedAutocorrelationLeftReflectedIntegrable_of_regularAnalyticPackage_owner
      f regularAnalyticPackage)
    (zetaCompletedAutocorrelationLeftInverseGammaIntegrable_of_analyticPackage_owner
      f analyticPackage)
    (zetaCompletedAutocorrelationLeftArithmeticIntegralExchange_of_analyticPackage_owner
      f analyticPackage)
    (zetaCompletedAutocorrelationArithmeticEquality_of_analyticPackage_owner
      f analyticPackage)
    (zetaCompletedAutocorrelationInverseGammaDifferenceIntegral_of_analyticPackage_owner
      f analyticPackage)
    (zetaCompletedAutocorrelationArchimedeanValue_of_inverseGammaTransport_owner
      f
      (zetaCompletedAutocorrelationInverseGammaTransport_of_analyticPackage_owner
        f analyticPackage))

theorem zetaCompletedAutocorrelationAffinePacketData_of_analyticPackages_owner
    (f : ZetaAdmissibleFunction)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (regularAnalyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedAutocorrelationRegularFamily f).toContourFamily) :
    ZetaCompletedAutocorrelationAffinePacketData f :=
  ZetaCompletedAutocorrelationAffinePacketData.of_analyticPackage
    f analyticPackage regularAnalyticPackage

/-- Canonical affine packet data from the proved autocorrelation Phi control,
prime Fubini/value theorems, and Gamma/Binet inverse-Gamma transport. -/
theorem zetaCompletedAutocorrelationAffinePacketData_canonicalPhiGamma_owner
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedAutocorrelationAffinePacketData f :=
  zetaCompletedAutocorrelationAffinePacketData_of_componentFacts_owner
    f
    (zetaCompletedAutocorrelationRightPrimeIntegrable_canonicalPhi_owner f)
    (zetaCompletedAutocorrelationRightInverseGammaIntegrable_canonicalPhi_owner f)
    (zetaCompletedAutocorrelationLeftReflectedIntegrable_canonicalPhi_owner f)
    (zetaCompletedAutocorrelationLeftInverseGammaIntegrable_canonicalPhi_owner f)
    (zetaCompletedAutocorrelationLeftArithmeticIntegralExchange_canonicalPhi_owner f)
    (zetaCompletedAutocorrelationArithmeticEquality_canonicalPhi_owner f)
    (zetaCompletedAutocorrelationInverseGammaDifferenceIntegral_canonicalPhi_owner f)
    (zetaCompletedAutocorrelationArchimedeanValue_canonicalPhi_owner f)

/-- The affine packet data is constructed from the autocorrelation analytic and
completed-log-derivative controls. -/
theorem zetaCompletedAutocorrelationAffinePacketData_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog :
      CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    ZetaCompletedAutocorrelationAffinePacketData f :=
  zetaCompletedAutocorrelationAffinePacketData_of_analyticPackages_owner
    f
    (zetaCompletedAutocorrelationFamilyAnalyticPackage_of_logDerivControl
      f hPhi hLog)
    (zetaCompletedAutocorrelationRegularAnalyticPackage_of_logDerivControl
      f hPhi hLog)

/-- The affine packet data is constructed from concrete autocorrelation
completed-log-derivative control. -/
theorem zetaCompletedAutocorrelationAffinePacketData_of_concreteControl_owner
    (f : ZetaAdmissibleFunction)
    (hConcrete :
      CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaCompletedAutocorrelationAffinePacketData f :=
  zetaCompletedAutocorrelationAffinePacketData_of_logDerivControl_owner
    f
    ((zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      zetaPhiAutocorrelationConcreteControl_owner) f)
    ((completedZetaNegLogDerivControl_autocorrelation_of_concreteControl
      hConcrete) f)

/-- The affine packet data is constructed from split autocorrelation factor
controls. -/
theorem zetaCompletedAutocorrelationAffinePacketData_of_factorControls_owner
    (f : ZetaAdmissibleFunction)
    (hZetaSide :
      CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaCompletedAutocorrelationAffinePacketData f :=
  zetaCompletedAutocorrelationAffinePacketData_of_concreteControl_owner
    f
    (completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
      hZetaSide
      hInverseGamma)

/-- The affine packet data is constructed from global factor controls. -/
theorem zetaCompletedAutocorrelationAffinePacketData_of_globalFactorControls_owner
    (f : ZetaAdmissibleFunction)
    (hZetaSide : CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma : CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaCompletedAutocorrelationAffinePacketData f :=
  zetaCompletedAutocorrelationAffinePacketData_of_factorControls_owner
    f
    (CompletedZetaNegLogDerivAutocorrelationZetaSideControl.ofZetaSideControl
      hZetaSide)
    (CompletedZetaNegLogDerivAutocorrelationInverseGammaControl.ofInverseGammaControl
      hInverseGamma)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
