import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Incidence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.InfinityCategory.Owner

/-!
# Boundary strata for geometric weights

This file owns the boundary-strata input for geometric-contour weights.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Boundary-stratum data used by geometric-contour weights.  It relates an object
of the stable interface to a boundary face of a contour-admissible bulk.
-/
structure GeometricWeightStratum
    (S : AnalyticMotivicStableInfinityInterface) where
  object : S.Object
  bulk : ContourAdmissibleBulk
  faceIndex : bulk.boundary.FaceIndex

namespace GeometricWeightStratum

/-- The boundary face associated to a geometric-weight stratum. -/
def face {S : AnalyticMotivicStableInfinityInterface}
    (W : GeometricWeightStratum S) :
    AnalyticBoundaryFace W.bulk.boundary.compactification :=
  W.bulk.boundary.face W.faceIndex

/-- The stable-interface object carrying a geometric-weight stratum. -/
def stableObject {S : AnalyticMotivicStableInfinityInterface}
    (W : GeometricWeightStratum S) : S.Object :=
  W.object

end GeometricWeightStratum

end AnalyticMotives
end LFunctions
end Boundary
