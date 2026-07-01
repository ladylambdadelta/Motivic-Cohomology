import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Faces.Owner

/-!
# Incidence of boundary faces

This file owns incidence data among boundary faces.  It is upstream of residue
filtrations and geometric-contour weight data.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Incidence data between two boundary faces of the same compactification.  The
map of strata must commute with the two maps into the compactified bulk.
-/
structure AnalyticBoundaryIncidence {X : AnalyticBulkCore}
    {K : AnalyticBulkCompactification X}
    (lower upper : AnalyticBoundaryFace K) where
  stratumMap : AnalyticBulkCoreHom lower.stratum upper.stratum
  commutes :
    AnalyticBulkCoreHom.comp stratumMap upper.inclusion = lower.inclusion

namespace AnalyticBoundaryIncidence

/-- The map on strata carried by boundary-incidence data. -/
def map {X : AnalyticBulkCore} {K : AnalyticBulkCompactification X}
    {lower upper : AnalyticBoundaryFace K}
    (I : AnalyticBoundaryIncidence lower upper) :
    AnalyticBulkCoreHom lower.stratum upper.stratum :=
  I.stratumMap

/-- The defining commutative triangle for boundary-incidence data. -/
theorem map_commutes {X : AnalyticBulkCore} {K : AnalyticBulkCompactification X}
    {lower upper : AnalyticBoundaryFace K}
    (I : AnalyticBoundaryIncidence lower upper) :
    AnalyticBulkCoreHom.comp I.stratumMap upper.inclusion = lower.inclusion :=
  I.commutes

end AnalyticBoundaryIncidence

end AnalyticMotives
end LFunctions
end Boundary
