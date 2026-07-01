import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRealization.BoundaryPresentations.Owner

/-!
# Bulk-to-boundary trace presentation

This file owns comparison statements from bulk analytic contour data to its
boundary trace presentation.  It does not define the bulk category by boundary
data.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Bulk-to-boundary trace comparison.  It attaches a boundary trace presentation
to a contour-admissible bulk without defining the bulk by that presentation.
-/
structure BulkToBoundaryTraceComparison where
  bulk : ContourAdmissibleBulk
  boundaryPresentation : BoundaryTracePresentation
  same_bulk :
    boundaryPresentation.boundaryStream.bulk = bulk

namespace BulkToBoundaryTraceComparison

/-- The downstream boundary presentation attached to the bulk. -/
def boundary (C : BulkToBoundaryTraceComparison) :
    BoundaryTracePresentation :=
  C.boundaryPresentation

/-- The bulk recorded by the boundary presentation. -/
theorem boundary_bulk_eq (C : BulkToBoundaryTraceComparison) :
    C.boundaryPresentation.boundaryStream.bulk = C.bulk :=
  C.same_bulk

end BulkToBoundaryTraceComparison

end AnalyticMotives
end LFunctions
end Boundary
