import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Core.Owner

/-!
# Identity contour-compatible correspondences

This file owns identity data for contour-compatible analytic correspondences.
It is downstream from support, transport, and residue compatibility, and
upstream from category-law packaging.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Identity data for a contour-admissible bulk in the contour-correspondence
calculus.  It records the diagonal correspondence together with its contour
transport and residue compatibility.
-/
structure ContourCorrespondenceIdentityData
    (X : ContourAdmissibleBulk) where
  identity : ContourAnalyticCorrespondence X X

namespace ContourCorrespondenceIdentityData

/-- The identity contour-compatible correspondence selected for a bulk. -/
def correspondence {X : ContourAdmissibleBulk}
    (I : ContourCorrespondenceIdentityData X) :
    ContourAnalyticCorrespondence X X :=
  I.identity

end ContourCorrespondenceIdentityData

end AnalyticMotives
end LFunctions
end Boundary
