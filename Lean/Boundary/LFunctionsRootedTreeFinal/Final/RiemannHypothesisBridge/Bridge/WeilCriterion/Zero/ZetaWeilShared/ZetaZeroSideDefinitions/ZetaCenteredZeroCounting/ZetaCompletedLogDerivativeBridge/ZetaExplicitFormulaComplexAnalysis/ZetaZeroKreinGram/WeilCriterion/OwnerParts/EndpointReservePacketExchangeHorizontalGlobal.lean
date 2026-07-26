import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.EndpointReservePacketExchangeHorizontal

/-!
# Endpoint reserve packet exchange from global factor controls

This owner part keeps the package-horizontal packet-exchange lane split after
the carrier-local Cauchy data has been supplied.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Canonical scheduled Cauchy path data and global factor controls give raw
Weil positivity through the corrected package-horizontal lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetExchange_globalLogDerivFactorControls_packageHorizontal_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  let hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
    ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner
  let hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
    ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_concreteControl
      (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_globalFactorControls
        hZetaSide
        hInverseGamma)
  zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetExchange_packageHorizontal_owner
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

/-- Carrier-level Cauchy data and global factor controls give raw Weil
positivity through the corrected package-horizontal lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_packetExchange_globalLogDerivFactorControls_packageHorizontal_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (zetaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaRadius f)
    (zetaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaAmplitude f)
    (zetaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaValueLower f)
    (gammaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaRadius f)
    (gammaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaAmplitude f)
    (gammaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaValueLower f)
    (zetaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
          (Metric.ball z (zetaRadius f)))
    (gammaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius f)))
    (zetaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius f) →
          ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
            zetaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (gammaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius f) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (zetaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        zetaValueLower f ≤ ‖ZetaAdmissibleFunction.zetaSideFactor z‖)
    (gammaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        gammaValueLower f ≤ ‖(Complex.Gammaℝ z)⁻¹‖)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_packetExchange_splitLogDerivControls_packageHorizontal_owner
    K
    zetaRadius
    zetaAmplitude
    zetaValueLower
    gammaRadius
    gammaAmplitude
    gammaValueLower
    zetaRadius_pos
    zetaAmplitude_pos
    zetaValueLower_pos
    gammaRadius_pos
    gammaAmplitude_pos
    gammaValueLower_pos
    zetaDiffCont
    gammaDiffCont
    zetaSphereBound
    gammaSphereBound
    zetaValueLower_bound
    gammaValueLower_bound
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl.ofZetaSideControl
      hZetaSide)
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl.ofInverseGammaControl
      hInverseGamma)

end

end LFunctions
end Boundary
