import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Correspondences.FiniteRectangleSupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Correspondences.FiniteRectangleTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Correspondences.FiniteRectangleResidueCompatibility.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Core.Owner

/-!
# RH finite rectangles as contour-compatible correspondences

This file is the owner target for the first real morphism-level constructor:

```text
finite-rectangle correspondence support
-> finite-rectangle contour transport
-> finite-rectangle residue compatibility
-> ContourAnalyticCorrespondence
```

Downstream `ContourCor_Q` files should not consume finite-rectangle relation
correspondences as generic morphisms until this constructor exists.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

end AnalyticMotives
end LFunctions
end Boundary
