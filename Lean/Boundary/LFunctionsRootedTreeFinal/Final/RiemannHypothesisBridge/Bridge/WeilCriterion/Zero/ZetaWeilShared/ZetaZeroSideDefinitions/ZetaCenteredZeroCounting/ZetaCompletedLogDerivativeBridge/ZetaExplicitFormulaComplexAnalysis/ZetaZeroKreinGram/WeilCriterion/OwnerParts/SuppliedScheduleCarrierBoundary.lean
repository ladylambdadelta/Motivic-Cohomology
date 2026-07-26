import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.SuppliedScheduleCarrierDataPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineScheduledPolynomialLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PolynomialPhysicalBoundaryHorizontal
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PositivityBridgeSummedPrime
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathAnalyticPacket

/-!
# Boundary identification from supplied quantitative carrier data

This owner part connects the supplied-schedule carrier Cauchy package to the
polynomial physical boundary lane and then to the trace-Bessel positivity
bridge.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- Affine packet data supplies the full right affine-kernel integrability for
the supplied-carrier endpoint route. -/
theorem zetaCompletedRightAffineKernel_integrable_of_suppliedPacketData_owner
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ∀ f : ZetaAdmissibleFunction,
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
        (volume : Measure ℝ) :=
  fun f =>
    ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightAffineKernel_integrable_of_packetExchange_owner
      f
      (packetData f).right_prime_integrable
      (packetData f).right_inverse_gamma_integrable

/-- Affine packet data supplies the full left affine-kernel integrability for
the supplied-carrier endpoint route. -/
theorem zetaCompletedLeftAffineKernel_integrable_of_suppliedPacketData_owner
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ∀ f : ZetaAdmissibleFunction,
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
        (volume : Measure ℝ) :=
  fun f =>
    ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftAffineKernel_integrable_of_packetExchange_owner
      f
      (packetData f).left_reflected_integrable

/-- Affine packet data supplies the full right-minus-left affine value identity
for the supplied-carrier endpoint route. -/
theorem zetaCompletedAffineKernel_integral_eq_physical_of_suppliedPacketData_owner
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ∀ f : ZetaAdmissibleFunction,
      (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f)
            t) -
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f)
            t) =
          ZetaAdmissibleFunction.explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f) :=
  fun f =>
    ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffineKernel_integral_eq_physical_of_packetExchange_owner
      f
      (packetData f).right_prime_integrable
      (packetData f).right_inverse_gamma_integrable
      (packetData f).left_reflected_integrable
      (packetData f).left_inverse_gamma_integrable
      (packetData f).left_arithmetic_integral_exchange
      (packetData f).arithmetic_equality
      (packetData f).inverse_gamma_difference_integral
      (packetData f).archimedean_value

/-- Supplied quantitative carrier data plus full-line affine-kernel
integrability and value identification gives the affine-channel endpoint. -/
theorem zetaCompletedAffineChannel_tendsto_physical_of_suppliedCarrierFamily_integrable_value_owner
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)) :
    ∀ f : ZetaAdmissibleFunction,
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f)
            (((carrierFamily.toLogDerivFamily).scheduledPolynomialPackage f).height_schedule.height u))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f))) :=
  fun f =>
    ZetaAdmissibleFunction.zetaCompletedAutocorrelationPolynomialScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
      f
      ((carrierFamily.toLogDerivFamily).scheduledPolynomialPackage f)
      (rightIntegrable f)
      (leftIntegrable f)
      (valueEquality f)

/-- A supplied quantitative carrier family and affine-channel endpoint give the
exact autocorrelation boundary identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_suppliedCarrierFamily_affineChannelLimit_owner
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              (((carrierFamily.toLogDerivFamily).scheduledPolynomialPackage f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledAffineChannelLimit_packageHorizontal_owner
    (carrierFamily.toLogDerivFamily).scheduledPolynomialPackage
    channelBoundaryLimit

/-- Supplied quantitative carrier data plus full-line affine-kernel
integrability and value identification give the exact autocorrelation boundary
identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_suppliedCarrierFamily_affineKernelIntegrableValue_owner
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_suppliedCarrierFamily_affineChannelLimit_owner
    carrierFamily
    (zetaCompletedAffineChannel_tendsto_physical_of_suppliedCarrierFamily_integrable_value_owner
      carrierFamily
      rightIntegrable
      leftIntegrable
      valueEquality)

/-- A supplied quantitative carrier family and physical boundary endpoint give
the exact autocorrelation boundary identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_suppliedCarrierFamily_boundaryLimit_owner
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f ((carrierFamily.toLogDerivFamily).scheduledPolynomialPackage f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledBoundaryLimit_packageHorizontal_owner
    (carrierFamily.toLogDerivFamily).scheduledPolynomialPackage
    boundaryLimit

/-- Supplied quantitative carrier data and an affine-channel endpoint give raw
Weil positivity through the trace-Bessel bridge. -/
theorem zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_affineChannelLimit_traceBessel_owner
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              (((carrierFamily.toLogDerivFamily).scheduledPolynomialPackage f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_owner
    zetaWeilQuadraticPositivity_canonicalBranch
    zetaWeilQuadraticPositivity_canonicalPartialOneTwo
    zetaWeilQuadraticPositivity_canonicalCompactOneTwo
    zetaWeilQuadraticPositivity_canonicalRightCriticalGrowth
    zetaWeilQuadraticPositivity_canonicalPartialLeft
    zetaWeilQuadraticPositivity_canonicalCompactBoundary
    (zetaWeilAutocorrelationBoundaryIdentification_of_suppliedCarrierFamily_affineChannelLimit_owner
      carrierFamily
      channelBoundaryLimit)

/-- Supplied quantitative carrier data plus full-line affine-kernel
integrability and value identification give raw Weil positivity through the
trace-Bessel bridge. -/
theorem zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_affineKernelIntegrableValue_traceBessel_owner
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_affineChannelLimit_traceBessel_owner
    carrierFamily
    (zetaCompletedAffineChannel_tendsto_physical_of_suppliedCarrierFamily_integrable_value_owner
      carrierFamily
      rightIntegrable
      leftIntegrable
      valueEquality)

/-- Supplied quantitative carrier data and affine packet data give raw Weil
positivity through the trace-Bessel bridge. -/
theorem zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_packetData_traceBessel_owner
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_affineKernelIntegrableValue_traceBessel_owner
    carrierFamily
    (zetaCompletedRightAffineKernel_integrable_of_suppliedPacketData_owner
      packetData)
    (zetaCompletedLeftAffineKernel_integrable_of_suppliedPacketData_owner
      packetData)
    (zetaCompletedAffineKernel_integral_eq_physical_of_suppliedPacketData_owner
      packetData)

/-- Supplied quantitative carrier data and global factor controls give raw Weil
positivity through the trace-Bessel bridge. -/
theorem zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_globalFactorControls_traceBessel_owner
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_packetData_traceBessel_owner
    carrierFamily
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffinePacketData_of_globalFactorControls_owner
        f
        hZetaSide
        hInverseGamma)

/-- Supplied quantitative carrier data and a physical boundary endpoint give raw
Weil positivity through the trace-Bessel bridge. -/
theorem zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_boundaryLimit_traceBessel_owner
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f ((carrierFamily.toLogDerivFamily).scheduledPolynomialPackage f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_owner
    zetaWeilQuadraticPositivity_canonicalBranch
    zetaWeilQuadraticPositivity_canonicalPartialOneTwo
    zetaWeilQuadraticPositivity_canonicalCompactOneTwo
    zetaWeilQuadraticPositivity_canonicalRightCriticalGrowth
    zetaWeilQuadraticPositivity_canonicalPartialLeft
    zetaWeilQuadraticPositivity_canonicalCompactBoundary
    (zetaWeilAutocorrelationBoundaryIdentification_of_suppliedCarrierFamily_boundaryLimit_owner
      carrierFamily
      boundaryLimit)

end
end LFunctions
end Boundary
