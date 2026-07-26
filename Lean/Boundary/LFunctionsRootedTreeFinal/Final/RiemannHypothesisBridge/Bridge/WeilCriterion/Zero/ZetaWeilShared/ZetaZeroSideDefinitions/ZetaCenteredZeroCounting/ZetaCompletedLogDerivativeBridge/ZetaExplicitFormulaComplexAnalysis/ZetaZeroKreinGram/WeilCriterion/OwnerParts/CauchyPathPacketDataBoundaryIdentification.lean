import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathBoundaryIdentification
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathAnalyticPacket
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PositivePacketAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathDataFromCarrier

/-!
# Boundary identification from affine packet data

This owner part converts the narrow affine packet-data object into the older
component packet-exchange surface for the Cauchy-path boundary identification
lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_packetData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_packetExchange_owner
    K
    zetaData
    gammaData
    (fun f => (packetData f).right_prime_integrable)
    (fun f => (packetData f).right_inverse_gamma_integrable)
    (fun f => (packetData f).left_reflected_integrable)
    (fun f => (packetData f).left_inverse_gamma_integrable)
    (fun f => (packetData f).left_arithmetic_integral_exchange)
    (fun f => (packetData f).arithmetic_equality)
    (fun f => (packetData f).inverse_gamma_difference_integral)
    (fun f => (packetData f).archimedean_value)

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_analyticPackages_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_packetData_owner
    K
    zetaData
    gammaData
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffinePacketData_of_analyticPackages_owner
        f
        (analyticPackage f)
        (regularAnalyticPackage f))

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetData_boundaryIdentification_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_owner
    zetaWeilQuadraticPositivity_canonicalBranch
    zetaWeilQuadraticPositivity_canonicalPartialOneTwo
    zetaWeilQuadraticPositivity_canonicalCompactOneTwo
    zetaWeilQuadraticPositivity_canonicalRightCriticalGrowth
    zetaWeilQuadraticPositivity_canonicalPartialLeft
    zetaWeilQuadraticPositivity_canonicalCompactBoundary
    (zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_packetData_owner
      K
      zetaData
      gammaData
      packetData)

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_analyticPackages_boundaryIdentification_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
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
  zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_owner
    zetaWeilQuadraticPositivity_canonicalBranch
    zetaWeilQuadraticPositivity_canonicalPartialOneTwo
    zetaWeilQuadraticPositivity_canonicalCompactOneTwo
    zetaWeilQuadraticPositivity_canonicalRightCriticalGrowth
    zetaWeilQuadraticPositivity_canonicalPartialLeft
    zetaWeilQuadraticPositivity_canonicalCompactBoundary
    (zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_analyticPackages_owner
      K
      zetaData
      gammaData
      analyticPackage
      regularAnalyticPackage)

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetData_direct_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetData_traceBessel_owner
    K
    zetaData
    gammaData
    packetData

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_packetData_traceBessel_owner
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
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetData_direct_traceBessel_owner
    K
    (fun f =>
      ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData.ofCarrierCauchyData
        f
        (K f)
        (zetaRadius f)
        (zetaAmplitude f)
        (zetaValueLower f)
        (zetaRadius_pos f)
        (zetaAmplitude_pos f)
        (zetaValueLower_pos f)
        (zetaDiffCont f)
        (zetaSphereBound f)
        (zetaValueLower_bound f))
    (fun f =>
      ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData.ofCarrierCauchyData
        f
        (K f)
        (gammaRadius f)
        (gammaAmplitude f)
        (gammaValueLower f)
        (gammaRadius_pos f)
        (gammaAmplitude_pos f)
        (gammaValueLower_pos f)
        (gammaDiffCont f)
        (gammaSphereBound f)
        (gammaValueLower_bound f))
    packetData

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_globalFactorControls_traceBessel_owner
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
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_packetData_traceBessel_owner
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
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffinePacketData_of_globalFactorControls_owner
        f
        hZetaSide
        hInverseGamma)

end

end LFunctions
end Boundary
