import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PositivityNormalizationInputs
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PositivityBridgeSummedPrime
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalBoundaryIdentificationHorizontalTransports
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PolynomialPhysicalBoundaryTransports
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathPacketExchangePositivity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathAnalyticPacket

/-!
# Completed-Weil positive assembly

This owner part reduces the final completed-Weil positivity theorem to the
single contour/boundary identification input.  The normalization, trace-Bessel,
ledger, and endpoint-Schur inputs are all owner-proved here.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- Completed-Weil positivity from the corrected autocorrelation boundary
identification. -/
theorem zetaWeilQuadraticPositivity_of_boundaryIdentification_traceBessel_owner
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_owner
    zetaWeilPositivity_binetBranchTailAbsorption_owner
    zetaWeilPositivity_boundaryLineOneAbelPartialMajorant_owner
    zetaWeilPositivity_oneTwoStripCompactBoundaryBound_owner
    zetaWeilPositivity_rightCriticalStripAdmissibleGrowth_owner
    zetaWeilPositivity_reflectedBoundaryAbelPartialMajorant_owner
    zetaWeilPositivity_rightCriticalStripCompactBoundaryBound_owner
    boundaryIdentification

/-- Completed-Weil positivity from direct completed-log-derivative control on
the physical autocorrelation probes. -/
theorem zetaWeilQuadraticPositivity_of_physicalLogDerivativeControl_horizontal_traceBessel_owner
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_traceBessel_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_physicalLogDerivControl_horizontal_owner
      hLog)

/-- Completed-Weil positivity from split log-derivative controls through the
corrected package-horizontal boundary identification. -/
theorem zetaWeilQuadraticPositivity_of_splitLogDerivativeControls_horizontal_traceBessel_owner
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_traceBessel_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_splitLogDerivativeControls_horizontal_owner
      hZetaSide
      hInverseGamma)

/-- Completed-Weil positivity from global zeta-side and inverse-Gamma
log-derivative controls through the corrected package-horizontal boundary
identification. -/
theorem zetaWeilQuadraticPositivity_of_globalLogDerivativeFactorControls_horizontal_traceBessel_owner
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_splitLogDerivativeControls_horizontal_traceBessel_owner
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl.ofZetaSideControl
      hZetaSide)
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl.ofInverseGammaControl
      hInverseGamma)

/-- Completed-Weil positivity from factor bounds on the canonical scheduled
carrier and the affine full-line value identity. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierFactorData_affineKernelIntegrableValue_traceBessel_owner
    (factorData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_traceBessel_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierFactorData_affineKernelIntegrableValue_owner
      factorData
      rightIntegrable
      leftIntegrable
      valueEquality)

/-- Completed-Weil positivity from the two canonical scheduled-carrier factor
estimates and the affine full-line value identity. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierBoundData_affineKernelIntegrableValue_traceBessel_owner
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.ZetaSideBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.InverseGammaBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierFactorData_affineKernelIntegrableValue_traceBessel_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_factorData_of_parts
        f
        (zetaData f)
        (gammaData f))
    rightIntegrable
    leftIntegrable
    valueEquality

/-- Completed-Weil positivity from explicit polynomial completed-log-derivative
bounds on the canonical scheduled top and bottom paths, together with the
affine full-line value identity.

This is the non-uniform scheduled lane: it does not require a uniform singular
separation bound on the entire infinite scheduled carrier. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_affineKernelIntegrableValue_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (C : ZetaAdmissibleFunction → ℝ)
    (C_pos : ∀ f : ZetaAdmissibleFunction, 0 < C f)
    (topBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTopPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (bottomBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBottomPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_traceBessel_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledPolynomialPathBounds_affineChannelLimit_owner
      K
      C
      C_pos
      topBound
      bottomBound
      (fun f =>
        ZetaAdmissibleFunction.zetaCompletedAutocorrelationPolynomialScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
          f
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_pathBounds
            f
            (K f)
            (C f)
            (C_pos f)
            (topBound f)
            (bottomBound f))
          (rightIntegrable f)
          (leftIntegrable f)
          (valueEquality f)))

/-- Completed-Weil positivity from explicit polynomial scheduled path bounds
and packet-exchange component identities. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_packetExchange_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (C : ZetaAdmissibleFunction → ℝ)
    (C_pos : ∀ f : ZetaAdmissibleFunction, 0 < C f)
    (topBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTopPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (bottomBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBottomPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
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
  zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_affineKernelIntegrableValue_traceBessel_owner
    K
    C
    C_pos
    topBound
    bottomBound
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

/-- Completed-Weil positivity from polynomial scheduled horizontal bounds and
explicit analytic-package packet data.

This is the cleaned owner surface: horizontal decay comes from the
scheduled-polynomial lane, while the vertical affine packet comes from the
analytic package and the separate archimedean transport value. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_analyticPacket_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (C : ZetaAdmissibleFunction → ℝ)
    (C_pos : ∀ f : ZetaAdmissibleFunction, 0 < C f)
    (topBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTopPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (bottomBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBottomPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (analyticPackage :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (regularAnalyticPackage :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedAutocorrelationRegularFamily f).toContourFamily)
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
  zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_packetExchange_traceBessel_owner
    K
    C
    C_pos
    topBound
    bottomBound
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightPrimeIntegrable_of_analyticPackage_owner
        f
        (analyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightInverseGammaIntegrable_of_analyticPackage_owner
        f
        (analyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftReflectedIntegrable_of_regularAnalyticPackage_owner
        f
        (regularAnalyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftInverseGammaIntegrable_of_analyticPackage_owner
        f
        (analyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftArithmeticIntegralExchange_of_analyticPackage_owner
        f
        (analyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationArithmeticEquality_of_analyticPackage_owner
        f
        (analyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationInverseGammaDifferenceIntegral_of_analyticPackage_owner
        f
        (analyticPackage f))
    archimedeanValue

/-- Completed-Weil positivity from polynomial scheduled horizontal bounds,
analytic-package packet facts, and inverse-Gamma transport to the Hermitian
archimedean kernel. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_analyticPacketTransport_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (C : ZetaAdmissibleFunction → ℝ)
    (C_pos : ∀ f : ZetaAdmissibleFunction, 0 < C f)
    (topBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTopPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (bottomBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBottomPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (analyticPackage :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (regularAnalyticPackage :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedAutocorrelationRegularFamily f).toContourFamily)
    (inverseGammaTransport :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
          ∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedHermitianInverseGammaIntegrand
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) t) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_analyticPacket_traceBessel_owner
    K
    C
    C_pos
    topBound
    bottomBound
    analyticPackage
    regularAnalyticPackage
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationArchimedeanValue_of_inverseGammaTransport_owner
        f
        (inverseGammaTransport f))

/-- Completed-Weil positivity from polynomial scheduled horizontal bounds and
explicit analytic packages for the canonical affine packet. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_analyticPackages_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (C : ZetaAdmissibleFunction → ℝ)
    (C_pos : ∀ f : ZetaAdmissibleFunction, 0 < C f)
    (topBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTopPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (bottomBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBottomPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (analyticPackage :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (regularAnalyticPackage :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedAutocorrelationRegularFamily f).toContourFamily) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_analyticPacketTransport_traceBessel_owner
    K
    C
    C_pos
    topBound
    bottomBound
    analyticPackage
    regularAnalyticPackage
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationInverseGammaTransport_of_analyticPackage_owner
        f
        (analyticPackage f))

end

end LFunctions
end Boundary
