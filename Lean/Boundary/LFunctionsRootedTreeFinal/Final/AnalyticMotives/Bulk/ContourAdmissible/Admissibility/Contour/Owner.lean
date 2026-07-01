import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.ContourSystem.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Admissibility.Boundary.Owner

/-!
# Contour-system admissibility data

This file owns the contour-exhaustion component selected for a boundary system.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Contour-system data selected for a boundary-admissible analytic bulk. -/
structure ContourSystemAdmissibility {X : AnalyticBulkCore}
    {K : CompactificationAdmissibility X}
    (B : BoundaryAdmissibility K) where
  system : AnalyticContourSystem B.system

namespace ContourSystemAdmissibility

/-- The selected contour system. -/
def data {X : AnalyticBulkCore}
    {K : CompactificationAdmissibility X}
    {B : BoundaryAdmissibility K}
    (C : ContourSystemAdmissibility B) :
    AnalyticContourSystem B.system :=
  C.system

/-- The selected contour exhaustion. -/
def exhaustion {X : AnalyticBulkCore}
    {K : CompactificationAdmissibility X}
    {B : BoundaryAdmissibility K}
    (C : ContourSystemAdmissibility B) :
    AnalyticContourExhaustion B.system :=
  C.system.exhaustion

/-- The contour chain at a selected stage. -/
def chainAt {X : AnalyticBulkCore}
    {K : CompactificationAdmissibility X}
    {B : BoundaryAdmissibility K}
    (C : ContourSystemAdmissibility B)
    (s : C.system.exhaustion.Stage) :
    AnalyticContourChain B.system :=
  C.system.chainAt s

end ContourSystemAdmissibility

end AnalyticMotives
end LFunctions
end Boundary
