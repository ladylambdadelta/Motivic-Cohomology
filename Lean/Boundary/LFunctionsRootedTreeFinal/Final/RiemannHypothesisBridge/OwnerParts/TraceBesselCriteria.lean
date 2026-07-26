import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.TraceBesselCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalContourBoundary
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.SuppliedScheduleCarrierBoundary
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.SuppliedScheduleCarrierCanonicalAssembly

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- Trace-Bessel summed-prime transport gives the Weil positivity input
directly from the boundary identification. -/
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_traceBessel
    (hBoundary : ZetaWeilAutocorrelationBoundaryIdentification) :
    ZetaWeilQuadraticPositivity :=
  finalRiemannHypothesis_zetaWeilQuadraticPositivity_traceBessel_core
    hBoundary

theorem finalRiemannHypothesis_boundaryIdentification_of_logDerivControl
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_logDerivControl_owner hPhi hLog

theorem finalRiemannHypothesis_boundaryIdentification_of_scheduledPackageBoundaryLimit
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f (hScheduled f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_scheduledPackageBoundaryLimit_owner
    hScheduled
    boundaryLimit

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_logDerivControl_traceBessel
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilQuadraticPositivity :=
  finalRiemannHypothesis_zetaWeilQuadraticPositivity_traceBessel
    (finalRiemannHypothesis_boundaryIdentification_of_logDerivControl hPhi hLog)

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_scheduledPackageBoundaryLimit
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f (hScheduled f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  finalRiemannHypothesis_zetaWeilQuadraticPositivity_traceBessel
    (finalRiemannHypothesis_boundaryIdentification_of_scheduledPackageBoundaryLimit
      hScheduled
      boundaryLimit)

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_affineChannelLimit_traceBessel
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              ((carrierFamily.scheduledPolynomialPackage f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_affineChannelLimit_traceBessel_owner
    carrierFamily
    channelBoundaryLimit

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_affineKernelIntegrableValue_traceBessel
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
  zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_affineKernelIntegrableValue_traceBessel_owner
    carrierFamily
    rightIntegrable
    leftIntegrable
    valueEquality

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_packetData_traceBessel
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_packetData_traceBessel_owner
    carrierFamily
    packetData

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_globalFactorControls_traceBessel
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_globalFactorControls_traceBessel_owner
    carrierFamily
    hZetaSide
    hInverseGamma

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_canonicalPhi_globalFactorControls_traceBessel
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
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_canonicalPhi_globalFactorControls_traceBessel_owner
    K
    carrierData
    separated
    hZetaSide
    hInverseGamma

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_boundaryLimit_traceBessel
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (carrierFamily.scheduledPolynomialPackage f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_boundaryLimit_traceBessel_owner
    carrierFamily
    boundaryLimit

theorem finalRiemannHypothesis_canonicalPoleClearedRightCriticalStripAdmissibleGrowth :
    PoleClearedRightCriticalStripAdmissibleGrowth :=
  finalRiemannHypothesis_canonicalPoleClearedRightCriticalStripAdmissibleGrowth_core

theorem finalRiemannHypothesis_canonicalZeroTailSmallValuesOwnerRunge :
    ZeroTailSmallValuesOwnerRunge :=
  finalRiemannHypothesis_canonicalZeroTailSmallValuesOwnerRunge_core

theorem finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (hPositive : ZetaWeilQuadraticPositivity) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity_core
    hPositive

/-- Trace-Bessel summed-prime transport gives the centered-zero criterion
directly from the boundary identification. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_traceBessel
    (hBoundary : ZetaWeilAutocorrelationBoundaryIdentification) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_traceBessel_core
    hBoundary

theorem finalRiemannHypothesis_centeredZeroCriterion_of_suppliedCarrierFamily_affineChannelLimit_traceBessel
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              ((carrierFamily.scheduledPolynomialPackage f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)))) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_affineChannelLimit_traceBessel
      carrierFamily
      channelBoundaryLimit)

theorem finalRiemannHypothesis_centeredZeroCriterion_of_suppliedCarrierFamily_affineKernelIntegrableValue_traceBessel
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
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_affineKernelIntegrableValue_traceBessel
      carrierFamily
      rightIntegrable
      leftIntegrable
      valueEquality)

theorem finalRiemannHypothesis_centeredZeroCriterion_of_suppliedCarrierFamily_packetData_traceBessel
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_packetData_traceBessel
      carrierFamily
      packetData)

theorem finalRiemannHypothesis_centeredZeroCriterion_of_suppliedCarrierFamily_globalFactorControls_traceBessel
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_globalFactorControls_traceBessel
      carrierFamily
      hZetaSide
      hInverseGamma)

theorem finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_canonicalPhi_globalFactorControls_traceBessel
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
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_canonicalPhi_globalFactorControls_traceBessel
      K
      carrierData
      separated
      hZetaSide
      hInverseGamma)

theorem finalRiemannHypothesis_centeredZeroCriterion_of_suppliedCarrierFamily_boundaryLimit_traceBessel
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (carrierFamily.scheduledPolynomialPackage f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_boundaryLimit_traceBessel
      carrierFamily
      boundaryLimit)

theorem finalRiemannHypothesis_centeredZeroCriterion_of_logDerivControl_traceBessel
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_logDerivControl_traceBessel
      hPhi hLog)

end
end LFunctions
end Boundary
