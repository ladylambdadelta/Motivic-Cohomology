import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.FactorBoundData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledAnalyticPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineScheduledPhysicalLimit

/-!
# Physical boundary identification transports

This owner part converts the concrete scheduled physical boundary endpoints
into the exact autocorrelation boundary identification consumed by positivity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

def zetaAutocorrelationPhysicalFullAnalyticPackage_of_logDerivControl_owner
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f) :=
  fun f =>
    zetaAutocorrelationPhysicalAnalyticPackage
      f
      ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
        ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
      (hLog f)

def zetaAutocorrelationPhysicalScheduledFamilyAnalyticPackage_of_logDerivControl_owner
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f) :=
  fun f =>
    (zetaAutocorrelationPhysicalFullAnalyticPackage_of_logDerivControl_owner
      hLog f).toScheduledFamilyAnalyticPackage

theorem zetaWeilAutocorrelationBoundaryIdentification_of_scheduledPoleCorrectedBoundaryLimit_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_cleanScheduledPackageBoundaryLimit_owner
    hScheduled
    boundaryLimit

theorem zetaWeilAutocorrelationBoundaryIdentification_of_scheduledRawVerticalBoundaryLimit_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_scheduledPoleCorrectedBoundaryLimit_owner
    hScheduled
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_rawVerticalLimit
        f
        (hScheduled f)
        (rawBoundaryLimit f))

theorem zetaWeilAutocorrelationBoundaryIdentification_of_scheduledAffineChannelBoundaryLimit_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_scheduledPoleCorrectedBoundaryLimit_owner
    hScheduled
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
        f
        (hScheduled f)
        (channelBoundaryLimit f))

theorem zetaWeilAutocorrelationBoundaryIdentification_of_scheduledAffineKernelIntegrableValue_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_scheduledAffineChannelBoundaryLimit_owner
    hScheduled
    (fun f =>
      zetaCompletedScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        (hScheduled f).height_schedule
        (rightIntegrable f)
        (leftIntegrable f)
        (valueEquality f))

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierFactorData_boundaryLimit_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_scheduledPoleCorrectedBoundaryLimit_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
        f
        ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
          ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
        (factorData f))
    boundaryLimit

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierFactorData_affineChannelLimit_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierFactorData_boundaryLimit_owner
    factorData
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
        f
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
          f
          ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
            ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
          (factorData f))
        (channelBoundaryLimit f))

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierFactorData_affineKernelIntegrableValue_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierFactorData_affineChannelLimit_owner
    factorData
    (fun f =>
      zetaCompletedScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
          f
          ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
            ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
          (factorData f)).height_schedule
        (rightIntegrable f)
        (leftIntegrable f)
        (valueEquality f))

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierBoundData_affineKernelIntegrableValue_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierFactorData_affineKernelIntegrableValue_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_factorData_of_parts
        f
        (zetaData f)
        (gammaData f))
    rightIntegrable
    leftIntegrable
    valueEquality

theorem zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_logDerivControl_owner
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    ∀ f : ZetaAdmissibleFunction,
      Tendsto
        (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
          f
          ((zetaAutocorrelationPhysicalScheduledFamilyAnalyticPackage_of_logDerivControl_owner
            hLog) f))
        atTop
        (𝓝
          (zetaCompletedAffinePoleCorrectedBoundaryChannel
            (zetaAutocorrelationPhysicalProbe f))) :=
  fun f =>
    zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_affine_logDerivControl_owner
      f
      ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
        ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
      (hLog f)

/-- Direct completed-log-derivative control on the physical autocorrelation
probes constructs the common zero-side/physical-boundary limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_physicalLogDerivControl_owner
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_cleanScheduledPackageBoundaryLimit
    (zetaAutocorrelationPhysicalScheduledFamilyAnalyticPackage_of_logDerivControl_owner
      hLog)
    (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_logDerivControl_owner
      hLog)

theorem zetaWeilAutocorrelationBoundaryIdentification_of_physicalLogDerivControl_owner
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit_core
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_physicalLogDerivControl_owner
      hLog)

/-- Concrete autocorrelation completed-log-derivative control constructs the
common zero-side/physical-boundary limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_concreteLogDerivativeControl_owner
    (hLogConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_physicalLogDerivControl_owner
    (ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_concreteControl
      hLogConcrete)

theorem zetaWeilAutocorrelationBoundaryIdentification_of_concreteLogDerivativeControl_owner
    (hLogConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit_core
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_concreteLogDerivativeControl_owner
      hLogConcrete)

/-- Split zeta-side and inverse-Gamma completed-log-derivative controls
construct the common zero-side/physical-boundary limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_splitLogDerivativeControls_owner
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_concreteLogDerivativeControl_owner
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
      hZetaSide
      hInverseGamma)

theorem zetaWeilAutocorrelationBoundaryIdentification_of_splitLogDerivativeControls_owner
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit_core
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_splitLogDerivativeControls_owner
      hZetaSide
      hInverseGamma)

/-- Global completed-log-derivative factor-bound data constructs the common
zero-side/physical-boundary limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_globalFactorBoundData_owner
    (factorData :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
          ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_concreteLogDerivativeControl_owner
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorBoundData
      factorData)

/-- Global completed-log-derivative factor-bound data constructs the exact Weil
boundary identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_globalFactorBoundData_owner
    (factorData :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
          ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit_core
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_globalFactorBoundData_owner
      factorData)

end
end LFunctions
end Boundary
