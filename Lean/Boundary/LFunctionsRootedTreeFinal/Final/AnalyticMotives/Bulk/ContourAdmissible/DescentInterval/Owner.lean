import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Refinements.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.DescentInterval.DescentCovers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.DescentInterval.IntervalObject.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.DescentInterval.IntervalHomotopy.Owner

/-!
# Descent and interval admissibility for analytic bulks

This owner separates the covering and interval-homotopy inputs from the core
bulk object.  The conservative starting point is contour refinement together
with analytified algebraic descent data, so the later comparison with
`DM_gm(ℚ)_ℚ` has a controlled source.

Dependency order: descent covers and interval objects first, then interval
homotopy data.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Descent and interval data attached to a contour system.  This layer records the
chosen interval object and the refinement-generated descent covers used by the
first conservative localization calculus.
-/
structure AnalyticDescentIntervalData {X : AnalyticBulkCore}
    {B : AnalyticBoundarySystem X}
    (C : AnalyticContourSystem B) where
  interval : AnalyticIntervalObject X
  CoverIndex : Type
  cover : CoverIndex → AnalyticContourDescentCover C

namespace AnalyticDescentIntervalData

/-- The interval object selected by descent/interval data. -/
def intervalObject {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    {C : AnalyticContourSystem B}
    (D : AnalyticDescentIntervalData C) : AnalyticIntervalObject X :=
  D.interval

/-- A selected contour descent cover. -/
def coverAt {X : AnalyticBulkCore} {B : AnalyticBoundarySystem X}
    {C : AnalyticContourSystem B}
    (D : AnalyticDescentIntervalData C) (i : D.CoverIndex) :
    AnalyticContourDescentCover C :=
  D.cover i

end AnalyticDescentIntervalData

end AnalyticMotives
end LFunctions
end Boundary
