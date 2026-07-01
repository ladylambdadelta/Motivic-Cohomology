import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Compactification.Owner

/-!
# Boundary faces of compactified analytic bulks

This file owns boundary-face data attached to compactified analytic bulks.
Residue ledgers and contour boundary behavior refer to these faces.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A boundary face of a compactified analytic bulk.  The face is represented by a
stratum core together with its map into the compactified core.
-/
structure AnalyticBoundaryFace {X : AnalyticBulkCore}
    (K : AnalyticBulkCompactification X) where
  stratum : AnalyticBulkCore
  inclusion : AnalyticBulkCoreHom stratum K.compactified

namespace AnalyticBoundaryFace

/-- The stratum core underlying a boundary face. -/
def core {X : AnalyticBulkCore} {K : AnalyticBulkCompactification X}
    (F : AnalyticBoundaryFace K) : AnalyticBulkCore :=
  F.stratum

/-- The map from a boundary face into the compactified core. -/
def map {X : AnalyticBulkCore} {K : AnalyticBulkCompactification X}
    (F : AnalyticBoundaryFace K) :
    AnalyticBulkCoreHom F.stratum K.compactified :=
  F.inclusion

end AnalyticBoundaryFace

end AnalyticMotives
end LFunctions
end Boundary
