import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Recurrence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Factors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.VerticalStrip.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Sectorial.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Angular.Owner

/-!
# Vertical recurrence transport for Gamma

This file aggregates the thematic split of vertical-recurrence theorems for
Gamma transport on the strip and boundary. It preserves the original declaration
order and keeps downstream imports routed through the aggregator for compatibility.

**Module structure:**
- `Recurrence.Owner`: Recurrence product definitions and multiplicative transport
- `Factors.Owner`: Per-factor bounds on the vertical strip
- `VerticalStrip.Owner`: Product composition and largeness handling
- `Sectorial.Owner`: Sectorial Stirling normalized form
- `Angular.Owner`: Angular defects and radius-power bounds
-/

namespace Boundary
namespace LFunctions

-- Re-export all theorems from the thematic subdirectories for downstream compatibility.
-- The split sections own their theorems; this aggregator provides the import path for consumers.

end LFunctions
end Boundary
