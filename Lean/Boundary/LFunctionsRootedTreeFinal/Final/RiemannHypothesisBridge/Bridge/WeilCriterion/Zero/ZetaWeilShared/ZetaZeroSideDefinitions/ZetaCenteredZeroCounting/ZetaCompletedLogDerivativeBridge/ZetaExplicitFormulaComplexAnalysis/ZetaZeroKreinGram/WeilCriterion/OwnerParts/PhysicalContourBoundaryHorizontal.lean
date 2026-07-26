import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalScheduledBoundaryLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledNormalizedContourResidueHorizontal

/-!
# Physical contour boundary with explicit horizontal decay

This owner part assembles the physical common-limit and boundary-identification
surfaces from an explicit horizontal-decay theorem instead of forcing the
horizontal decay to come from a global scheduled carrier package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- The scheduled-package-native physical contour tends to the completed zero
side from explicit horizontal decay and eventual selected tangent-residue
equality. -/
theorem zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_tangentEventual_horizontal
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
    (htangentEventual :
      ∀ᶠ u in atTop,
        ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
            (zetaAutocorrelationPhysicalProbe f)
            (h.height_schedule.height u) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedTangentContourIntegral
            (zetaAutocorrelationPhysicalProbe f)
            ((zetaAutocorrelationPhysicalContourFamily f).rectangle
              (h.height_schedule.height u)))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.explicitFormulaScheduledPackageHorizontalSideDifference h u)
        atTop (𝓝 0)) :
    Tendsto
      (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical f h)
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  ZetaAdmissibleFunction.explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex_of_horizontal
    (zetaAutocorrelationPhysicalProbe f)
    (zetaAutocorrelationPhysicalContourFamily f)
    h
    htangentEventual
    hhorizontal
    (summable_zetaZeroSideContribution_owner
      (zetaAutocorrelationPhysicalProbe f))

/-- Scheduled packages with explicit tangent, horizontal, and boundary endpoint
limits construct the common pole-corrected physical contour limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_scheduledPackageEndpointLimits_horizontal
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (htangentEventual :
      ∀ f : ZetaAdmissibleFunction,
        ∀ᶠ u in atTop,
          ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
              (zetaAutocorrelationPhysicalProbe f)
              ((hScheduled f).height_schedule.height u) =
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedTangentContourIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                ((hScheduled f).height_schedule.height u)))
    (hhorizontal :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.explicitFormulaScheduledPackageHorizontalSideDifference
              (hScheduled f) u)
          atTop (𝓝 0))
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
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_limitFamily_core
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
        f (hScheduled f))
    (fun f =>
      zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_tangentEventual_horizontal
        f
        (hScheduled f)
        (htangentEventual f)
        (hhorizontal f))
    boundaryLimit

/-- Scheduled packages with explicit horizontal decay and a physical boundary
endpoint give the exact Weil boundary identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_scheduledPackageBoundaryLimit_horizontal_owner
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (htangentEventual :
      ∀ f : ZetaAdmissibleFunction,
        ∀ᶠ u in atTop,
          ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
              (zetaAutocorrelationPhysicalProbe f)
              ((hScheduled f).height_schedule.height u) =
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedTangentContourIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                ((hScheduled f).height_schedule.height u)))
    (hhorizontal :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.explicitFormulaScheduledPackageHorizontalSideDifference
              (hScheduled f) u)
          atTop (𝓝 0))
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
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_scheduledPackageEndpointLimits_horizontal
      hScheduled
      htangentEventual
      hhorizontal
      boundaryLimit)

end
end LFunctions
end Boundary
