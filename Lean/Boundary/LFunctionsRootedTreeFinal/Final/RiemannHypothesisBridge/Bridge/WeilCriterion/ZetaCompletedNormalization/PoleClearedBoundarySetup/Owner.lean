import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Analysis.Owner

/-!
# Pole-cleared zeta and boundary-line setup

This file aggregates the pole-clearing foundations, analytical properties, and
boundary-line computations. It preserves the original declaration order and keeps
downstream imports routed through `ZetaCompletedNormalization.Owner`.

**Module structure:**
- `Core.Owner`: Continuity, analyticity, compact bounds, general Stirling estimates
- `Analysis.Owner`: Boundary-line applications and Abel-Plana assembly
-/

namespace Boundary
namespace LFunctions

-- Re-export all theorems from Core and Analysis for downstream compatibility.
-- The split subdirectories own the theorems thematically; this file provides
-- the aggregator import path for consumers of PoleClearedBoundarySetup.

end LFunctions
end Boundary
