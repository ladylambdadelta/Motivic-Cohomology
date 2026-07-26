import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.BoundaryTraceBesselCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.TraceBesselCriteria
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.FactorBoundData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledPointwiseFactorBoundData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledAnalyticPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineScheduledPhysicalLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalBoundaryIdentificationTransports

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

theorem boundaryRiemannHypothesis_of_boundaryIdentification_traceBessel_owner
    (hBoundary : ZetaWeilAutocorrelationBoundaryIdentification) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_boundaryIdentification_traceBessel_core_owner
    hBoundary

theorem boundaryRiemannHypothesis_of_zeroSideBoundaryIdentification_traceBessel_owner
    (zeroBoundary :
      ZetaCompletedAutocorrelationZeroSideBoundaryIdentification) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_zeroSideBoundaryIdentification_traceBessel_core_owner
    zeroBoundary

theorem boundaryRiemannHypothesis_of_poleCorrectedCommonLimit_traceBessel_owner
    (commonLimit :
      ZetaCompletedAutocorrelationPoleCorrectedCommonLimit) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_poleCorrectedCommonLimit_traceBessel_core_owner
    commonLimit

theorem boundaryRiemannHypothesis_of_canonicalPoleCorrectedCommonLimit_owner
    (commonLimit :
      ZetaCompletedAutocorrelationPoleCorrectedCommonLimit) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_poleCorrectedCommonLimit_traceBessel_owner
    commonLimit

theorem boundaryRiemannHypothesis_of_scheduledPoleCorrectedEndpointLimits_owner
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (zeroLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f (hScheduled f))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f (hScheduled f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalPoleCorrectedCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_limitFamily_core
      (fun f =>
        zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
          f (hScheduled f))
      zeroLimit
      boundaryLimit)

theorem boundaryRiemannHypothesis_of_scheduledPoleCorrectedBoundaryLimit_owner
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_boundaryIdentification_traceBessel_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_scheduledPoleCorrectedBoundaryLimit_owner
      hScheduled
      boundaryLimit)

theorem boundaryRiemannHypothesis_of_scheduledRawVerticalBoundaryLimit_owner
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (rawBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                  ((hScheduled f).height_schedule.height u)) -
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                  ((hScheduled f).height_schedule.height u)))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_boundaryIdentification_traceBessel_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_scheduledRawVerticalBoundaryLimit_owner
      hScheduled
      rawBoundaryLimit)

theorem boundaryRiemannHypothesis_of_scheduledAffineChannelBoundaryLimit_owner
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_boundaryIdentification_traceBessel_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_scheduledAffineChannelBoundaryLimit_owner
      hScheduled
      channelBoundaryLimit)

theorem boundaryRiemannHypothesis_of_scheduledAffineKernelIntegrableValue_owner
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_boundaryIdentification_traceBessel_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_scheduledAffineKernelIntegrableValue_owner
      hScheduled
      rightIntegrable
      leftIntegrable
      valueEquality)

/-- Log-derivative control proves RH through the direct scheduled completed
affine channel, after forgetting the full analytic package to its scheduled
horizontal carrier. -/
theorem boundaryRiemannHypothesis_of_logDerivControl_scheduledAffine_owner
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_scheduledPoleCorrectedBoundaryLimit_owner
    (fun f =>
      (zetaAutocorrelationPhysicalAnalyticPackage
        f (hPhi f) (hLog f)).toScheduledFamilyAnalyticPackage)
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_affine_logDerivControl_owner
        f (hPhi f) (hLog f))

/-- RH from factor bounds on the canonical scheduled horizontal carrier and the
corresponding scheduled pole-corrected physical boundary limit. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_boundaryLimit_owner
    (factorData : ∀ f : ZetaAdmissibleFunction,
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_scheduledPoleCorrectedBoundaryLimit_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
        f
        ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
          ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
        (factorData f))
    boundaryLimit

/-- RH from factor bounds on the canonical scheduled horizontal carrier and the
direct completed affine-channel boundary limit. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_affineChannelLimit_owner
    (factorData : ∀ f : ZetaAdmissibleFunction,
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_scheduledAffineChannelBoundaryLimit_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
        f
        ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
          ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
        (factorData f))
    channelBoundaryLimit

/-- RH from factor bounds on the canonical scheduled horizontal carrier plus the
direct completed affine full-line integrability and value theorem. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_affineKernelIntegrableValue_owner
    (factorData : ∀ f : ZetaAdmissibleFunction,
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_scheduledAffineKernelIntegrableValue_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
        f
        ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
          ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
        (factorData f))
    rightIntegrable
    leftIntegrable
    valueEquality

/-- RH from canonical scheduled carrier factor bounds, component affine
integrability, and the completed affine full-line value theorem. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_affineComponentIntegrableValue_owner
    (factorData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_affineKernelIntegrableValue_owner
    factorData
    (fun f =>
      zetaCompletedRightAffineKernel_integrable_of_component_integrable_owner
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        (rightPrimeIntegrable f)
        (rightInverseGammaIntegrable f))
    (fun f =>
      zetaCompletedLeftAffineKernel_integrable_of_reflected_integrable_owner
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        (leftReflectedIntegrable f))
    valueEquality

/-- RH from canonical scheduled carrier factor bounds, component affine
integrability, and the completed affine packet value decomposition. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_affineComponentIntegrablePacketValue_owner
    (factorData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
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
    (packetValue :
      ∀ f : ZetaAdmissibleFunction,
        let probe : ZetaAdmissibleFunction :=
          ZetaAdmissibleFunction.convolutionAutocorrelation f
        let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
        let arithmeticValue : ℂ :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
            probe
        let archimedeanValue : ℂ :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
            probe
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
          ∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
          arithmeticValue + archimedeanValue) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_affineComponentIntegrableValue_owner
    factorData
    rightPrimeIntegrable
    rightInverseGammaIntegrable
    leftReflectedIntegrable
    (fun f =>
      let probe : ZetaAdmissibleFunction :=
        ZetaAdmissibleFunction.convolutionAutocorrelation f
      let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
        ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
      let arithmeticValue : ℂ :=
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
          probe
      let archimedeanValue : ℂ :=
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
          probe
      zetaCompletedAffineKernelIntegral_eq_physical_of_packet_value_owner
        probe family arithmeticValue archimedeanValue
        (packetValue f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution_div_twoPi_eq_primeContribution_autocorrelation
          f)
        (zetaCompletedAffinePhysicalBoundaryChannel_eq probe))

theorem boundaryRiemannHypothesis_of_scheduledPoleCorrectedBoundaryLimit_and_tangentResidue_owner
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (htangentEventual :
      ∀ f : ZetaAdmissibleFunction,
        ∀ᶠ u in atTop,
          ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((hScheduled f).height_schedule.height u) =
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedTangentContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((hScheduled f).height_schedule.height u)))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f (hScheduled f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_scheduledPoleCorrectedEndpointLimits_owner
    hScheduled
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_tangentEventual
        f
        (hScheduled f)
        (htangentEventual f))
    boundaryLimit

theorem boundaryRiemannHypothesis_of_logDerivControl_traceBessel_owner
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_logDerivControl_scheduledAffine_owner
    hPhi hLog

theorem boundaryRiemannHypothesis_of_logDerivBoundaryIdentification_traceBessel_owner
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_boundaryIdentification_traceBessel_owner
    (finalRiemannHypothesis_boundaryIdentification_of_logDerivControl hPhi hLog)

theorem boundaryRiemannHypothesis_of_canonicalPhi_logDerivControl_owner
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_logDerivControl_traceBessel_owner
    (ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner)
    hLog

theorem boundaryRiemannHypothesis_of_concreteLogDerivControl_owner
    (hPhiConcrete :
      ZetaAdmissibleFunction.ZetaPhiAutocorrelationConcreteControl)
    (hLogConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_logDerivControl_traceBessel_owner
    (ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      hPhiConcrete)
    (ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_concreteControl
      hLogConcrete)

theorem boundaryRiemannHypothesis_of_splitConcreteLogDerivControls_owner
    (hPhiConcrete :
      ZetaAdmissibleFunction.ZetaPhiAutocorrelationConcreteControl)
    (hZetaSide : ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma : ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_concreteLogDerivControl_owner
    hPhiConcrete
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
      hZetaSide
      hInverseGamma)

theorem boundaryRiemannHypothesis_of_analyticPhi_splitLogDerivControls_owner
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hZetaSide : ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma : ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_splitConcreteLogDerivControls_owner
    (ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_of_analyticControl hPhi)
    hZetaSide hInverseGamma

theorem boundaryRiemannHypothesis_of_analyticPhi_globalLogDerivFactorControls_owner
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hZetaSide : ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma : ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_analyticPhi_splitLogDerivControls_owner
    hPhi
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl.ofZetaSideControl
      hZetaSide)
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl.ofInverseGammaControl
      hInverseGamma)

theorem boundaryRiemannHypothesis_of_canonicalPhi_globalLogDerivFactorControls_owner
    (hZetaSide : ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma : ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_analyticPhi_globalLogDerivFactorControls_owner
    (ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner)
    hZetaSide
    hInverseGamma

theorem boundaryRiemannHypothesis_of_canonicalTransform_logDerivBoundData_owner
    (zetaData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.ZetaSideBoundData E)
    (gammaData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalPhi_logDerivControl_owner
    (ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_boundData_owner
      zetaData
      gammaData)

theorem boundaryRiemannHypothesis_of_canonicalTransform_logDerivFactorBoundData_owner
    (factorData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalPhi_logDerivControl_owner
    (ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_factorBoundData_owner
      factorData)

theorem boundaryRiemannHypothesis_of_canonicalTransform_completedLogDerivSuppliedConstants_owner
    (C :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (hCpos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < C f a b E N)
    (hCbound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖ZetaAdmissibleFunction.completedZetaNegLogDeriv z‖ ≤
          C f a b E N * (1 + ‖z.im‖) ^ N) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalPhi_logDerivControl_owner
    (ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_suppliedConstants_owner
      C
      hCpos
      hCbound)

theorem boundaryRiemannHypothesis_of_suppliedCarrierFamily_affineKernelIntegrableValue_traceBessel_owner
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_suppliedCarrierFamily_affineKernelIntegrableValue_traceBessel
      carrierFamily
      rightIntegrable
      leftIntegrable
      valueEquality)

theorem boundaryRiemannHypothesis_of_suppliedCarrierFamily_packetData_traceBessel_owner
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_suppliedCarrierFamily_packetData_traceBessel
      carrierFamily
      packetData)

theorem boundaryRiemannHypothesis_of_suppliedCarrierFamily_globalFactorControls_traceBessel_owner
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_suppliedCarrierFamily_globalFactorControls_traceBessel
      carrierFamily
      hZetaSide
      hInverseGamma)

theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_canonicalPhi_globalFactorControls_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (separated :
      ∀ f : ZetaAdmissibleFunction,
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
          f).HasPositiveSingularSeparation)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_canonicalPhi_globalFactorControls_traceBessel
      K
      carrierData
      separated
      hZetaSide
      hInverseGamma)

end
end LFunctions
end Boundary
