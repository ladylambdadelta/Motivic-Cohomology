import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledNormalizedContourResidueLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.RightHalfPlaneGrowth.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalBoundaryIdentificationCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalContourBoundaryCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.TailSummability.Owner

/-!
# Physical scheduled zero-side endpoint

This owner part contains the package-native pole-corrected vertical coordinate
and its zero-side endpoint theorem.  It is deliberately separated from the
physical boundary endpoint so downstream files do not import the historical
broad contour owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- The scheduled-package-native normalized pole-corrected completed contour in
the physical lane. -/
def zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f)) :
    ℝ → ℂ :=
  fun u : ℝ =>
    ZetaAdmissibleFunction.explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
      (zetaAutocorrelationPhysicalProbe f)
      (zetaAutocorrelationPhysicalContourFamily f)
      h
      u

/-- The scheduled-package-native physical contour tends to the completed zero
side once the selected tangent-residue identity holds eventually. -/
theorem zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_tangentEventual
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
              (h.height_schedule.height u))) :
    Tendsto
      (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical f h)
      atTop
      (𝓝
        (Boundary.LFunctions.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  ZetaAdmissibleFunction.explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex
    (zetaAutocorrelationPhysicalProbe f)
    (zetaAutocorrelationPhysicalContourFamily f)
    h
    htangentEventual
    (summable_zetaZeroSideContribution_owner
      (zetaAutocorrelationPhysicalProbe f))

/-- A scheduled analytic package supplies the physical scheduled-package
zero-side endpoint. -/
theorem zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_scheduledPackage
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f)) :
    Tendsto
      (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical f h)
      atTop
      (𝓝
        (Boundary.LFunctions.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_zeroSide_of_tangentEventual
    f
    h
    (ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_scheduledPackage
      (zetaAutocorrelationPhysicalProbe f)
      (zetaAutocorrelationPhysicalContourFamily f)
      h)

end
end LFunctions
end Boundary
