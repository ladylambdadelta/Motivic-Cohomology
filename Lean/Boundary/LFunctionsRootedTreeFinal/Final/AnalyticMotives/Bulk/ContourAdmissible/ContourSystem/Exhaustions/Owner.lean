import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Chains.Owner

/-!
# Contour exhaustions on analytic bulks

This file owns admissible contour-exhaustion data.  Deformations and
refinements are downstream from exhaustions.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
An indexed exhaustion of contour chains.  The preorder-like relation is kept as
data because the admissible refinement calculus is developed in the refinement
owner layer.
-/
structure AnalyticContourExhaustion {X : AnalyticBulkCore}
    (B : AnalyticBoundarySystem X) where
  Stage : Type
  chain : Stage → AnalyticContourChain B
  precedes : Stage → Stage → Type

namespace AnalyticContourExhaustion

/-- The contour chain at a stage of an exhaustion. -/
def chainAt {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    (E : AnalyticContourExhaustion B) (s : E.Stage) :
    AnalyticContourChain B :=
  E.chain s

end AnalyticContourExhaustion

end AnalyticMotives
end LFunctions
end Boundary
