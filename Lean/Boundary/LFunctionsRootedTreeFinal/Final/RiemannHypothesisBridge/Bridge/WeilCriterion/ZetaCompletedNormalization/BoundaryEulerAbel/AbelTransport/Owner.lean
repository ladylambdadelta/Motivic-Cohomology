import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.AbelTransport.Setup.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.AbelTransport.Dirichlet.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.AbelTransport.Continuation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.AbelTransport.Damping.Owner

/-!
# Abel transport for boundary zeta tails

This file aggregates the thematic split of Abel-transport theorems for the
boundary-line zeta computation. It preserves the original declaration order and
keeps downstream imports routed through the aggregator for compatibility.

**Module structure:**
- `Setup.Owner`: Endpoint and derivative contributions in finite Abel decompositions
- `Dirichlet.Owner`: Dirichlet series forms and oscillatory transforms
- `Continuation.Owner`: Boundary-point analysis and analytic continuation
- `Damping.Owner`: Abel damping, prefix behavior, and boundary limits
-/

namespace Boundary
namespace LFunctions

-- Re-export all theorems from the thematic subdirectories for downstream compatibility.
-- The split sections own their theorems; this aggregator provides the import path for consumers.

end LFunctions
end Boundary
