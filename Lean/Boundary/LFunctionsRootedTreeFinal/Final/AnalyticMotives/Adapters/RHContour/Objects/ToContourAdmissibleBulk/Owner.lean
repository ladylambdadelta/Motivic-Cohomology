import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Objects.FiniteRectangleBoundarySystem.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Objects.FiniteRectangleContourSystem.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Objects.FiniteRectangleResidueLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Objects.FiniteRectangleDescentInterval.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Owner

/-!
# RH finite rectangles as contour-admissible bulks

This file is the owner target for the first real object-level constructor:

```text
RHContourAdmissibleBulk -> ContourAdmissibleBulk
```

The constructor belongs here only after the boundary system, contour system,
residue ledger, and descent/interval data have been constructed in the sibling
files.  Downstream category files should not consume RH contour objects as full
analytic bulks until this file supplies that constructor.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

end AnalyticMotives
end LFunctions
end Boundary
