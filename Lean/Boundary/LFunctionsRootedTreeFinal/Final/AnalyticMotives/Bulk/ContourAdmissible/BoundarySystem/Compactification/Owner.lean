import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.Owner

/-!
# Compactifications of analytic bulks

This file owns compactification data for analytic bulk cores.  Boundary faces
and incidence relations are downstream from compactification.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A compactification datum for an analytic bulk core.  It records the compactified
core and the ordinary paired map from the open bulk into that compactification.
Closedness, properness, and boundary-face regularity are owned by later layers.
-/
structure AnalyticBulkCompactification (X : AnalyticBulkCore) where
  compactified : AnalyticBulkCore
  openMap : AnalyticBulkCoreHom X compactified

namespace AnalyticBulkCompactification

/-- The compactified core attached to a compactification datum. -/
def target {X : AnalyticBulkCore} (K : AnalyticBulkCompactification X) :
    AnalyticBulkCore :=
  K.compactified

/-- The open-bulk map into its compactification. -/
def inclusion {X : AnalyticBulkCore} (K : AnalyticBulkCompactification X) :
    AnalyticBulkCoreHom X K.compactified :=
  K.openMap

end AnalyticBulkCompactification

end AnalyticMotives
end LFunctions
end Boundary
