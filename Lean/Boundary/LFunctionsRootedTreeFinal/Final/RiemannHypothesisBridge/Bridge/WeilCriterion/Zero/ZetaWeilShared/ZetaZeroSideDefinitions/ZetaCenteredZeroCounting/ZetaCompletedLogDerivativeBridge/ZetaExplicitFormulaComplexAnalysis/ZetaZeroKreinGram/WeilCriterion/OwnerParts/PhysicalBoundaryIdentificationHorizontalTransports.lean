import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalBoundaryIdentificationTransports
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalContourBoundaryHorizontal

/-!
# Physical boundary identification through explicit horizontal decay

This owner part gives the log-derivative-control boundary identification using
the package-horizontal endpoint rather than the legacy scheduled shortcut.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- Log-derivative control supplies the package-horizontal side decay for the
scheduled physical autocorrelation package. -/
theorem zetaAutocorrelationPhysicalScheduledPackageHorizontalSideDifference_tendsto_zero_of_logDerivControl_owner
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    ∀ f : ZetaAdmissibleFunction,
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.explicitFormulaScheduledPackageHorizontalSideDifference
            ((zetaAutocorrelationPhysicalScheduledFamilyAnalyticPackage_of_logDerivControl_owner
              hLog) f) u)
        atTop (𝓝 0) :=
  fun f =>
    ZetaAdmissibleFunction.explicitFormulaScheduledPackageHorizontalSideDifference_tendsto_zero
      ((zetaAutocorrelationPhysicalScheduledFamilyAnalyticPackage_of_logDerivControl_owner
        hLog) f)
      1

/-- Log-derivative control supplies eventual equality between the pole-corrected
residue sum and the normalized tangent contour on the scheduled physical
autocorrelation package. -/
theorem zetaAutocorrelationPhysicalScheduledPackage_tangentEventual_of_logDerivControl_owner
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    ∀ f : ZetaAdmissibleFunction,
      ∀ᶠ u in atTop,
        ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
            (zetaAutocorrelationPhysicalProbe f)
            (((zetaAutocorrelationPhysicalScheduledFamilyAnalyticPackage_of_logDerivControl_owner
              hLog) f).height_schedule.height u) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedTangentContourIntegral
            (zetaAutocorrelationPhysicalProbe f)
            ((zetaAutocorrelationPhysicalContourFamily f).rectangle
              (((zetaAutocorrelationPhysicalScheduledFamilyAnalyticPackage_of_logDerivControl_owner
                hLog) f).height_schedule.height u)) :=
  fun f =>
    ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_scheduledPackage
      (zetaAutocorrelationPhysicalProbe f)
      (zetaAutocorrelationPhysicalContourFamily f)
      ((zetaAutocorrelationPhysicalScheduledFamilyAnalyticPackage_of_logDerivControl_owner
        hLog) f)

/-- Log-derivative control gives the exact boundary identification through the
corrected package-horizontal contour endpoint. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_physicalLogDerivControl_horizontal_owner
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_scheduledPackageBoundaryLimit_horizontal_owner
    (zetaAutocorrelationPhysicalScheduledFamilyAnalyticPackage_of_logDerivControl_owner
      hLog)
    (zetaAutocorrelationPhysicalScheduledPackage_tangentEventual_of_logDerivControl_owner
      hLog)
    (zetaAutocorrelationPhysicalScheduledPackageHorizontalSideDifference_tendsto_zero_of_logDerivControl_owner
      hLog)
    (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_logDerivControl_owner
      hLog)

/-- Concrete log-derivative control gives the exact boundary identification
through the corrected package-horizontal contour endpoint. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_concreteLogDerivativeControl_horizontal_owner
    (hLogConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_physicalLogDerivControl_horizontal_owner
    (ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_concreteControl
      hLogConcrete)

/-- Split factor log-derivative controls give the exact boundary identification
through the corrected package-horizontal contour endpoint. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_splitLogDerivativeControls_horizontal_owner
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_concreteLogDerivativeControl_horizontal_owner
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
      hZetaSide
      hInverseGamma)

end

end LFunctions
end Boundary
