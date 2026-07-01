import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Objects.FiniteRectangleBoundarySystem.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.Owner

/-!
# Finite-rectangle contour system target

This file is the owner target for constructing the contour-system component of
an `RHContourAdmissibleBulk`.

The intended construction uses:

* `ExplicitFormulaContourFamily.rectangle` as the height-indexed chain source;
* `ExplicitFormulaCofinalHeightSchedule` for cofinal contour exhaustion;
* boundary-avoidance theorems from `ZetaExplicitFormulaAnalyticPackage`;
* path regularity from the explicit-formula contour owner.

The proof target is a concrete `AnalyticContourSystem` for the finite-rectangle
boundary system, with stages supplied by the RH height schedule.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

end AnalyticMotives
end LFunctions
end Boundary
