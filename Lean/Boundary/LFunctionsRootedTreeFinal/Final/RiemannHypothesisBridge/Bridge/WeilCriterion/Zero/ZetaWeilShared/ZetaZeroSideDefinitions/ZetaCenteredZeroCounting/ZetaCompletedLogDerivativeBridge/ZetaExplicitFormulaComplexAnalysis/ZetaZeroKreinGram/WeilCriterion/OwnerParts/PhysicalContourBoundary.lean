import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalAnalyticInputs
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.AutocorrelationAnalyticPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledLogDerivControl
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledNormalizedContourResidueLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalContourBoundaryCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalBoundaryIdentificationCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffinePhysicalLimitFinal
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.NormalizedContourZeroSide
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.TailSummability.Owner

/-!
# Physical normalized contour boundary

The residue contour is normalized by `2 pi` and its pole packet is removed
before it is compared with the physical prime and archimedean boundary.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- The canonical analytic package for the physical autocorrelation contour. -/
def zetaAutocorrelationPhysicalAnalyticPackage
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
      (zetaAutocorrelationPhysicalProbe f)
      (zetaAutocorrelationPhysicalContourFamily f) :=
  ZetaAdmissibleFunction.CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
    f
    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
    hPhi
    hLog

/-- The scheduled normalized pole-corrected completed contour in the physical lane. -/
def zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    ℝ → ℂ :=
  fun u : ℝ =>
    ZetaAdmissibleFunction.explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference
      (zetaAutocorrelationPhysicalProbe f)
      (zetaAutocorrelationPhysicalContourFamily f)
      (zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog)
      u

/-- Pointwise selected tangent-residue equality on positive scheduled heights
supplies the physical scheduled-package zero-side endpoint. -/
theorem zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_tangentPointwise
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
    (hpointwise :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedTangentContourIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u)) =
            ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
              (zetaAutocorrelationPhysicalProbe f)
              (h.height_schedule.height u)) :
    Tendsto
      (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical f h)
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_tangentEventual
    f
    h
    (ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_scheduledPackage_pointwise
      (zetaAutocorrelationPhysicalProbe f)
      (zetaAutocorrelationPhysicalContourFamily f)
      h
      hpointwise)

/-- Pointwise raw Cauchy tangent-residue equality on positive scheduled heights
supplies the physical scheduled-package zero-side endpoint. -/
theorem zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_rawTangentPointwise
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
    (hraw :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTangentContourIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u)) =
            ZetaAdmissibleFunction.explicitFormulaTwoPiI •
              ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
                (zetaAutocorrelationPhysicalProbe f)
                (h.height_schedule.height u)) :
    Tendsto
      (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical f h)
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_tangentEventual
    f
    h
    (ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_scheduledPackage_rawPointwise
      (zetaAutocorrelationPhysicalProbe f)
      (zetaAutocorrelationPhysicalContourFamily f)
      h
      hraw)

/-- Scheduled boundary/interior data for the physical autocorrelation contour supply
the physical scheduled-package zero-side endpoint. -/
theorem zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_boundaryData
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
    (hinterior :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
            rho ∈ ZetaAdmissibleFunction.explicitFormulaCompletedZeroContourHeightWindow
                (h.height_schedule.height u) ↔
              ZetaAdmissibleFunction.completedZeroResidueCoordinate rho ∈
                  ZetaAdmissibleFunction.explicitFormulaContourFamilyInterior
                    (zetaAutocorrelationPhysicalContourFamily f)
                    (h.height_schedule.height u) ∧
                ZetaAdmissibleFunction.completedZeroResidueCoordinate rho ∈
                  ZetaAdmissibleFunction.completedZetaContourIntegrandSingularSet)
    (hboundaryRegular :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          ∀ z : ℂ,
            z ∈
                ZetaAdmissibleFunction.explicitFormulaContourFamilyBoundary
                  (zetaAutocorrelationPhysicalContourFamily f)
                  (h.height_schedule.height u) →
              ContinuousAt
                  (fun w : ℂ =>
                    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegrand
                      (zetaAutocorrelationPhysicalProbe f) w) z ∧
                DifferentiableAt ℂ
                  (fun w : ℂ =>
                    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegrand
                      (zetaAutocorrelationPhysicalProbe f) w) z)
    (hboundaryAvoidance :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          ∀ z : ℂ,
            z ∈
                ZetaAdmissibleFunction.explicitFormulaContourFamilyBoundary
                  (zetaAutocorrelationPhysicalContourFamily f)
                  (h.height_schedule.height u) →
              z ∉ ZetaAdmissibleFunction.completedZetaContourIntegrandSingularSet) :
    Tendsto
      (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical f h)
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_tangentEventual
    f
    h
    (ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_scheduledPackage_boundaryData
      (zetaAutocorrelationPhysicalProbe f)
      (zetaAutocorrelationPhysicalContourFamily f)
      h
      hinterior
      hboundaryRegular
      hboundaryAvoidance)

/-- A common contour limit identifies the zero-side series with the pole-corrected boundary. -/
theorem zetaCompletedAutocorrelationZeroSideBoundaryIdentification_of_commonLimit
    (commonLimit : ZetaCompletedAutocorrelationPoleCorrectedCommonLimit) :
    ZetaCompletedAutocorrelationZeroSideBoundaryIdentification :=
  zetaCompletedAutocorrelationZeroSideBoundaryIdentification_of_commonLimit_core
    commonLimit

/-- The canonical scheduled normalized contour tends to the completed zero side. -/
theorem zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical_tendsto_zeroSide
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f))
    (zeroSideSummable :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ)
            (zetaAutocorrelationPhysicalProbe f))) :
    Tendsto
      (zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical f hPhi hLog)
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  Exists.elim
    (zetaAutocorrelationPhysicalAnalyticPackage
      f hPhi hLog).scheduled_horizontalFamilyZeroExcisedStrip
    (fun carrier carrierSpec =>
      ZetaAdmissibleFunction.explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f)
        (zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog)
        carrier carrierSpec.1 carrierSpec.2 zeroSideSummable)

/-- The canonical scheduled normalized contour tends to the physical pole-corrected boundary. -/
theorem zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical_tendsto_boundary
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    Tendsto
      (zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical f hPhi hLog)
      atTop
      (𝓝
        (zetaCompletedAffinePoleCorrectedBoundaryChannel
          (zetaAutocorrelationPhysicalProbe f))) :=
  zetaCompletedExplicitFormulaAutocorrelationNormalizedPoleCorrectedVertical_tendsto_completedBoundary_sub_poles_owner
    f hPhi hLog

/-- The scheduled-package physical vertical tends to the pole-corrected boundary
when the scheduled package is obtained by forgetting a full analytic package. -/
theorem zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_logDerivControl
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    Tendsto
      (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
        f
        ((zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog).toScheduledFamilyAnalyticPackage))
      atTop
      (𝓝
        (zetaCompletedAffinePoleCorrectedBoundaryChannel
          (zetaAutocorrelationPhysicalProbe f))) :=
  let fullPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f) :=
    zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog
  let packageFunctionEquality :
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
          f fullPackage.toScheduledFamilyAnalyticPackage =
        zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical f hPhi hLog :=
    funext
      (fun u : ℝ =>
        ZetaAdmissibleFunction.explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference_of_fullPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f)
          fullPackage
          u)
  Eq.subst
    (motive := fun values : ℝ → ℂ =>
      Tendsto values atTop
        (𝓝
          (zetaCompletedAffinePoleCorrectedBoundaryChannel
            (zetaAutocorrelationPhysicalProbe f))))
    packageFunctionEquality.symm
    (zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical_tendsto_boundary
      f hPhi hLog)

/-- The two endpoint limit theorems assemble into the common-limit surface. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_endpointLimits
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f))
    (zeroSideSummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
            zetaZeroSideContribution (rho : ℂ)
              (zetaAutocorrelationPhysicalProbe f))) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  fun f =>
    ⟨zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical f (hPhi f) (hLog f),
      zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical_tendsto_zeroSide
        f (hPhi f) (hLog f) (zeroSideSummable f),
      zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical_tendsto_boundary
        f (hPhi f) (hLog f)⟩

/-- A pointwise family with the two physical endpoint limits constructs the
common-limit surface consumed by zero-side boundary identification. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_limitFamily
    (φ : ∀ f : ZetaAdmissibleFunction, ℝ → ℂ)
    (zeroLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto (φ f) atTop
          (𝓝
            (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto (φ f) atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_limitFamily_core
    φ
    zeroLimit
    boundaryLimit

/-- Scheduled analytic packages with the two physical endpoint limits construct
the common-limit surface without passing through full arbitrary-strip
log-derivative control. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_scheduledPackageEndpointLimits
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (zeroLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f (hScheduled f))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
              (zetaAutocorrelationPhysicalProbe f))))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f (hScheduled f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_limitFamily
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
        f (hScheduled f))
    zeroLimit
    boundaryLimit

/-- Scheduled analytic packages plus the physical boundary endpoint construct
the common-limit surface; the zero-side endpoint is supplied by the scheduled
selected-radius residue owner chain. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_scheduledPackageBoundaryLimit
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
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_scheduledPackageEndpointLimits
    hScheduled
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_scheduledPackage
        f
        (hScheduled f))
    boundaryLimit

/-- A scheduled analytic package plus its pole-corrected physical boundary
endpoint gives the exact Weil boundary identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_scheduledPackageBoundaryLimit_owner
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
  zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit_core
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_scheduledPackageBoundaryLimit
      hScheduled
      boundaryLimit)

/-- Full log-derivative controls construct the common-limit surface through the
narrow scheduled-package endpoint lane. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_logDerivControl_scheduledPackage
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_scheduledPackageBoundaryLimit
    (fun f =>
      (zetaAutocorrelationPhysicalAnalyticPackage f (hPhi f) (hLog f)).toScheduledFamilyAnalyticPackage)
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_logDerivControl
        f
        (hPhi f)
        (hLog f))

/-- Existing contour controls construct the common normalized pole-corrected contour limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_logDerivControl
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (zeroSideSummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
            zetaZeroSideContribution (rho : ℂ)
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_endpointLimits
    hPhi hLog zeroSideSummable

/-- The zero-side summability input to the common-limit construction is owned by the
completed-zero tail summability layer, so the only remaining analytic input here is
completed log-derivative strip control on autocorrelation probes. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_logDerivControl_owner
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_logDerivControl
    hPhi
    hLog
    (fun f =>
      summable_zetaZeroSideContribution_owner
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))

/-- The zero-side boundary identification implies the real Weil-form boundary identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_zeroSideBoundaryIdentification
    (zeroBoundary :
      ZetaCompletedAutocorrelationZeroSideBoundaryIdentification) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_zeroSideBoundaryIdentification_core
    zeroBoundary

/-- The completed zero side equals the normalized pole-corrected boundary on an autocorrelation
probe by uniqueness of the canonical normalized completed-affine limit. -/
theorem zetaCompletedZeroSideComplex_convolutionAutocorrelation_eq_poleCorrectedBoundaryChannel_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (zeroSideSummable :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ)
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
    ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedAffinePoleCorrectedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  let zeroLimit :
      Tendsto
        (zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical f hPhi hLog)
        atTop
          (𝓝
            (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
              (zetaAutocorrelationPhysicalProbe f))) :=
    zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical_tendsto_zeroSide
      f hPhi hLog zeroSideSummable
  let physicalLimit :
      Tendsto
        (zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical f hPhi hLog)
        atTop
        (𝓝
          (zetaCompletedAffinePoleCorrectedBoundaryChannel
            (zetaAutocorrelationPhysicalProbe f))) :=
    zetaAutocorrelationPhysicalScheduledPoleCorrectedVertical_tendsto_boundary
      f hPhi hLog
  tendsto_nhds_unique zeroLimit physicalLimit

/-- The normalized contour formula identifies the completed Weil form as the
real pole-corrected completed boundary. -/
theorem zetaWeilFormCompleted_convolutionAutocorrelation_eq_poleCorrectedBoundaryChannel_re_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (zeroSideSummable :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ)
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
    zetaWeilFormCompleted
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      Complex.re
        (zetaCompletedAffinePoleCorrectedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
  let zeroToBoundary :
      ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletedAffinePoleCorrectedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
    zetaCompletedZeroSideComplex_convolutionAutocorrelation_eq_poleCorrectedBoundaryChannel_owner
      f hPhi hLog zeroSideSummable
  Eq.trans
    (zetaWeilFormCompleted_convolutionAutocorrelation_eq_zeroSide f)
    (congrArg Complex.re zeroToBoundary)

/-- The log-derivative-controlled contour identification supplies the exact boundary
identification consumed by the positivity bridge. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_logDerivControl
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (zeroSideSummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
            zetaZeroSideContribution (rho : ℂ)
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_zeroSideBoundaryIdentification
    (zetaCompletedAutocorrelationZeroSideBoundaryIdentification_of_commonLimit
      (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_logDerivControl
        hPhi hLog zeroSideSummable))

/-- Autocorrelation log-derivative strip control supplies the exact boundary
identification consumed by the positivity bridge; zero-side summability is supplied by
the completed-zero tail summability owner. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_logDerivControl_owner
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_scheduledPackageBoundaryLimit_owner
    (fun f =>
      (zetaAutocorrelationPhysicalAnalyticPackage f (hPhi f) (hLog f)).toScheduledFamilyAnalyticPackage)
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_logDerivControl
        f
        (hPhi f)
        (hLog f))

/-- The common-limit statement supplies the exact boundary identification consumed by
the positivity bridge. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit
    (commonLimit : ZetaCompletedAutocorrelationPoleCorrectedCommonLimit) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit_core
    commonLimit

end

end LFunctions
end Boundary
