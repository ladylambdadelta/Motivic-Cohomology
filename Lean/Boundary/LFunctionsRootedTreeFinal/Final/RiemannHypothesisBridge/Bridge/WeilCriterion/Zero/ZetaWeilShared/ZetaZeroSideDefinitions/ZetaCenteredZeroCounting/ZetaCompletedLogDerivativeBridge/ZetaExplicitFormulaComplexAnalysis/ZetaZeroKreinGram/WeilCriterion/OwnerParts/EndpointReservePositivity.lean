import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PositivityTraceReductions
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.EndpointAbsorbedSignedBoundary
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalBoundaryIdentificationTransports
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorption

/-!
# Endpoint reserve positivity

This file connects the endpoint-absorbed signed-boundary trace reserve to the
Weil positivity owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- Canonical Binet branch input for endpoint-reserve positivity. -/
theorem zetaWeilQuadraticPositivity_canonicalBranch :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption :=
  Complex.binetSecondFormulaBranchUniformTailAbsorption_owner

/-- Canonical reflected pole-cleared envelope input for endpoint-reserve
positivity. -/
theorem zetaWeilQuadraticPositivity_canonicalReflectedEnvelope :
    PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope :=
  poleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope_owner

/-- Canonical one-two boundary Abel partial majorant for endpoint-reserve
positivity. -/
theorem zetaWeilQuadraticPositivity_canonicalPartialOneTwo :
    BoundaryLineOneAbelPartialMajorant :=
  boundaryLineOneAbelPartialMajorant_from_realParam

/-- Canonical one-two compact boundary bound for endpoint-reserve positivity. -/
theorem zetaWeilQuadraticPositivity_canonicalCompactOneTwo :
    PoleClearedOneTwoStripCompactBoundaryBound :=
  poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact

/-- Canonical right-critical-strip growth input for endpoint-reserve positivity. -/
theorem zetaWeilQuadraticPositivity_canonicalRightCriticalGrowth :
    PoleClearedRightCriticalStripAdmissibleGrowth :=
  poleClearedRightCriticalStripAdmissibleGrowth_owner
    zetaWeilQuadraticPositivity_canonicalBranch
    zetaWeilQuadraticPositivity_canonicalReflectedEnvelope

/-- Canonical reflected boundary Abel partial majorant for endpoint-reserve
positivity. -/
theorem zetaWeilQuadraticPositivity_canonicalPartialLeft :
    ReflectedBoundaryAbelPartialMajorant :=
  reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
    zetaWeilQuadraticPositivity_canonicalPartialOneTwo

/-- Canonical right-critical-strip compact boundary bound for endpoint-reserve
positivity. -/
theorem zetaWeilQuadraticPositivity_canonicalCompactBoundary :
    PoleClearedRightCriticalStripCompactBoundaryBound :=
  poleClearedRightCriticalStripCompactBoundaryBound_from_compact

/-- Endpoint reserve domination gives nonnegativity of the endpoint-absorbed
physical scalar. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_endpointReserveDomination_owner
    (reserveDomination :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedEndpointTraceReserveDomination f) :
    ∀ f : ZetaAdmissibleFunction,
      0 ≤ ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f :=
  fun f =>
    ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_traceReserveDomination
      f (reserveDomination f)

/-- Endpoint reserve domination gives nonnegativity of the canonical
endpoint-absorbed physical scalar. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_owner
    (reserveDomination :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedEndpointTraceReserveDomination f) :
    ∀ f : ZetaAdmissibleFunction,
      0 ≤ ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f :=
  completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_endpointReserveDomination_owner
    reserveDomination

/-- Completed Weil positivity follows once the positive trace reserve absorbs
both endpoint diagonal debt and negative archimedean variation. -/
theorem zetaWeilQuadraticPositivity_of_endpointTraceReserveDomination_owner
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification)
    (reserveDomination :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedEndpointTraceReserveDomination f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_endpointAbsorbedPhysical_owner
    boundaryIdentification
    (completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_endpointReserveDomination_owner
      reserveDomination)

/-- Completed Weil positivity from the physical endpoint-absorption owner and
the exact autocorrelation boundary identification. -/
theorem zetaWeilQuadraticPositivity_of_endpointPhysicalAbsorption_owner
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_endpointAbsorbedPhysical_owner
    boundaryIdentification
    (fun f =>
      ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_owner
        f)

/-- Completed Weil positivity from the physical endpoint-absorption owner and
the exact autocorrelation boundary identification, using the canonical contour
inputs. -/
theorem zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_endpointPhysicalAbsorption_owner
    boundaryIdentification

/-- Completed Weil positivity from the selector-free pole-corrected common
limit.  This is the narrow final analytic sink: uniqueness of limits gives the
boundary identification, and endpoint absorption gives positivity. -/
theorem zetaWeilQuadraticPositivity_of_poleCorrectedCommonLimit_owner
    (commonLimit : ZetaCompletedAutocorrelationPoleCorrectedCommonLimit) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit_core
      commonLimit)

/-- Completed Weil positivity from autocorrelation physical log-derivative
control.  The physical contour owner supplies the boundary identification, and
endpoint absorption supplies the signed positivity transfer. -/
theorem zetaWeilQuadraticPositivity_of_physicalLogDerivControl_owner
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_physicalLogDerivControl_owner
      hLog)

/-- Completed Weil positivity from a concrete autocorrelation completed
log-derivative control package. -/
theorem zetaWeilQuadraticPositivity_of_concreteLogDerivativeControl_owner
    (hLogConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_concreteLogDerivativeControl_owner
      hLogConcrete)

/-- Completed Weil positivity from the split zeta-side and inverse-Gamma
autocorrelation completed-log-derivative controls. -/
theorem zetaWeilQuadraticPositivity_of_splitLogDerivativeControls_owner
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_splitLogDerivativeControls_owner
      hZetaSide
      hInverseGamma)

/-- Completed Weil positivity after the boundary-identification owner and the
endpoint-reserve owner have both supplied their concrete conclusions. -/
theorem zetaWeilQuadraticPositivity_of_boundaryIdentification_and_endpointTraceReserveDomination_owner
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification)
    (reserveDomination :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedEndpointTraceReserveDomination f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_endpointTraceReserveDomination_owner
    boundaryIdentification
    reserveDomination

theorem zetaWeilQuadraticPositivity_of_scheduledPoleCorrectedBoundaryLimit_owner
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f (hScheduled f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_scheduledPoleCorrectedBoundaryLimit_owner
      hScheduled
      boundaryLimit)

theorem zetaWeilQuadraticPositivity_of_scheduledAffineChannelBoundaryLimit_owner
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((hScheduled f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_scheduledAffineChannelBoundaryLimit_owner
      hScheduled
      channelBoundaryLimit)

theorem zetaWeilQuadraticPositivity_of_scheduledAffineKernelIntegrableValue_owner
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
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
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_scheduledAffineKernelIntegrableValue_owner
      hScheduled
      rightIntegrable
      leftIntegrable
      valueEquality)

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierFactorData_boundaryLimit_owner
    (factorData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
              f
              ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
                ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
              (factorData f)))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierFactorData_boundaryLimit_owner
      factorData
      boundaryLimit)

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierFactorData_affineChannelLimit_owner
    (factorData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
                f
                ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
                  ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
                (factorData f)).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierFactorData_affineChannelLimit_owner
      factorData
      channelBoundaryLimit)

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierFactorData_affineKernelIntegrableValue_owner
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
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierFactorData_affineKernelIntegrableValue_owner
      factorData
      rightIntegrable
      leftIntegrable
      valueEquality)

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierBoundData_affineKernelIntegrableValue_owner
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
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierBoundData_affineKernelIntegrableValue_owner
      zetaData
      gammaData
      rightIntegrable
      leftIntegrable
      valueEquality)

theorem zetaWeilQuadraticPositivity_of_polynomialScheduledEndpointLimits_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (zeroLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (hPolynomial f))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (hPolynomial f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledEndpointLimits_owner
      hPolynomial
      zeroLimit
      boundaryLimit)

theorem zetaWeilQuadraticPositivity_of_polynomialScheduledProjectContourBoundaryLimits_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (projectLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((hPolynomial f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (hPolynomial f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledProjectContourBoundaryLimits_owner
      hPolynomial
      projectLimit
      boundaryLimit)

theorem zetaWeilQuadraticPositivity_of_polynomialScheduledTangentBoundaryLimits_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (tangentEventual :
      ∀ f : ZetaAdmissibleFunction,
        ∀ᶠ u in atTop,
          ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((hPolynomial f).height_schedule.height u) =
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedTangentContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((hPolynomial f).height_schedule.height u)))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (hPolynomial f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledTangentBoundaryLimits_owner
      hPolynomial
      tangentEventual
      boundaryLimit)

theorem zetaWeilQuadraticPositivity_of_polynomialScheduledAffineChannelLimit_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (zeroLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (hPolynomial f))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((hPolynomial f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_polynomialScheduledEndpointLimits_owner
    hPolynomial
    zeroLimit
    (fun f =>
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
        f
        (hPolynomial f)
        (channelBoundaryLimit f))

theorem zetaWeilQuadraticPositivity_of_polynomialScheduledAffineKernelIntegrableValue_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (zeroLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (hPolynomial f))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
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
  zetaWeilQuadraticPositivity_of_polynomialScheduledAffineChannelLimit_owner
    hPolynomial
    zeroLimit
    (fun f =>
      zetaCompletedScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        (hPolynomial f).height_schedule
        (rightIntegrable f)
        (leftIntegrable f)
        (valueEquality f))

theorem zetaWeilQuadraticPositivity_of_polynomialScheduledProjectContourAffineChannelLimit_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (projectLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((hPolynomial f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((hPolynomial f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_polynomialScheduledProjectContourBoundaryLimits_owner
    hPolynomial
    projectLimit
    (fun f =>
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
        f
        (hPolynomial f)
        (channelBoundaryLimit f))

theorem zetaWeilQuadraticPositivity_of_polynomialScheduledTangentAffineChannelLimit_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (tangentEventual :
      ∀ f : ZetaAdmissibleFunction,
        ∀ᶠ u in atTop,
          ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((hPolynomial f).height_schedule.height u) =
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedTangentContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((hPolynomial f).height_schedule.height u)))
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((hPolynomial f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_polynomialScheduledTangentBoundaryLimits_owner
    hPolynomial
    tangentEventual
    (fun f =>
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
        f
        (hPolynomial f)
        (channelBoundaryLimit f))

/-- Completed Weil positivity from endpoint reserve domination in the
standard completed-boundary coordinate. -/
theorem zetaWeilQuadraticPositivity_completedBoundary_owner
    (boundaryIdentification :
      ZetaWeilAutocorrelationCompletedBoundaryIdentification)
    (physicalArchimedeanAbsorption :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.zetaCompletedArchimedeanNegativeVariationScalar f ≤
          ZetaAdmissibleFunction.zetaCompletedPhysicalPrimeBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedPhysicalCorrectionBoundaryScalar f +
            ZetaAdmissibleFunction.zetaCompletedArchimedeanPositiveVariationScalar f) :
    ZetaWeilQuadraticPositivity :=
  physicalArchimedeanAbsorption_to_zetaWeilQuadraticPositivity_of_boundaryIdentification
    boundaryIdentification
    physicalArchimedeanAbsorption

end

end LFunctions
end Boundary
