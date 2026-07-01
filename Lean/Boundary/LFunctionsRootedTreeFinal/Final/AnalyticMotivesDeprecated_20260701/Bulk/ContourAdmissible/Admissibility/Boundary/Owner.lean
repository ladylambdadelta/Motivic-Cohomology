import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Admissibility.Compactification.Owner

/-!
# Boundary-system admissibility data

This file owns the boundary component of a contour-admissible analytic bulk.
The data is indexed by a selected compactification admissibility layer so the
object assembly can avoid one monolithic structure.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Boundary-system data selected for a compactified analytic bulk core. -/
structure BoundaryAdmissibility {X : AnalyticBulkCore}
    (K : CompactificationAdmissibility X) where
  system : AnalyticBoundarySystem X
  compactification_match :
    system.compactification = K.compactification

namespace BoundaryAdmissibility

/-- The selected boundary system. -/
def data {X : AnalyticBulkCore}
    {K : CompactificationAdmissibility X}
    (B : BoundaryAdmissibility K) :
    AnalyticBoundarySystem X :=
  B.system

/-- The selected boundary face at an index. -/
def faceAt {X : AnalyticBulkCore}
    {K : CompactificationAdmissibility X}
    (B : BoundaryAdmissibility K)
    (i : B.system.FaceIndex) :
    AnalyticBoundaryFace B.system.compactification :=
  B.system.faceAt i

/-- The boundary system uses the selected compactification. -/
theorem compactification_eq {X : AnalyticBulkCore}
    {K : CompactificationAdmissibility X}
    (B : BoundaryAdmissibility K) :
    B.system.compactification = K.compactification :=
  B.compactification_match

end BoundaryAdmissibility

end AnalyticMotives
end LFunctions
end Boundary
