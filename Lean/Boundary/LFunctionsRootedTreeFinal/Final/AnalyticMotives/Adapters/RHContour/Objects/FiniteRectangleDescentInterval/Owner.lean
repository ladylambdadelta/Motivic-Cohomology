import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Objects.FiniteRectangleResidueLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.DescentInterval.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.HorizontalDecay.Owner

/-!
# Finite-rectangle descent and interval target

This file is the owner target for constructing the descent/interval component
of an `RHContourAdmissibleBulk`.

The intended construction uses:

* countable bad-height avoidance;
* controlled contour refinements from cofinal height schedules;
* horizontal decay as the analytic control for ignoring horizontal boundary
  error in the realization layer;
* a selected interval parameter only after its endpoint/projection laws are
  proved from the contour construction.

The first descent topology should remain conservative: contour refinements and
analytified algebraic Nisnevich generators only.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

end AnalyticMotives
end LFunctions
end Boundary
