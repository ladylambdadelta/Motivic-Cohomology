import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Adapters.RHContour.Correspondences.FiniteRectangleResidueCompatibility.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Constructed.Owner

/-!
# Finite-rectangle identity and composition targets

This file is the owner target for constructing identity and composition of
finite-rectangle contour-compatible correspondences.

The intended proof chain is:

```text
diagonal finite-rectangle support
-> identity transport
-> identity residue compatibility
-> fiber-product support composition
-> composed transport
-> composed residue compatibility
-> identity and associativity laws
```

No category-law record should be accepted here unless its fields are filled
from the preceding concrete definitions.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

end AnalyticMotives
end LFunctions
end Boundary
