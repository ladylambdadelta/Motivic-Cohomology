import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.DescentInterval.DescentCovers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Admissibility.Contour.Owner

/-!
# Descent admissibility data

This file owns the conservative descent-cover component used before
localization.  The first intended covers are contour refinements and
analytified algebraic descent covers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent covers selected for a contour system. -/
structure DescentAdmissibility {X : AnalyticBulkCore}
    {K : CompactificationAdmissibility X}
    {B : BoundaryAdmissibility K}
    (C : ContourSystemAdmissibility B) where
  CoverIndex : Type
  cover : CoverIndex → AnalyticContourDescentCover C.system

namespace DescentAdmissibility

/-- A selected descent cover. -/
def coverAt {X : AnalyticBulkCore}
    {K : CompactificationAdmissibility X}
    {B : BoundaryAdmissibility K}
    {C : ContourSystemAdmissibility B}
    (D : DescentAdmissibility C) (i : D.CoverIndex) :
    AnalyticContourDescentCover C.system :=
  D.cover i

end DescentAdmissibility

end AnalyticMotives
end LFunctions
end Boundary
