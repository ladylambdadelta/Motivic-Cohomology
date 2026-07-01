import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Objects.ToContourAdmissibleBulk.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Support.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.Owner

/-!
# Finite-rectangle correspondence supports

This file is the owner target for support-level RH finite-rectangle
correspondences.

The intended construction starts only after
`RHContourAdmissibleBulk -> ContourAdmissibleBulk` exists.  It should then build
analytic support data inside the product of two contour-admissible bulks and
prove the source/target finiteness properties from the concrete support
construction.

The existing singular-support relation model can be used here as a local test
adapter, but the final support object must be a genuine
`AnalyticCorrespondenceSupport`, not a relation-only replacement for it.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

end AnalyticMotives
end LFunctions
end Boundary
