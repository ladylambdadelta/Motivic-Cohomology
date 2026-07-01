import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Compactification.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Faces.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.BoundarySystem.Incidence.Owner

/-!
# Boundary systems for analytic bulks

Boundary systems record compactification faces and incidence data for analytic
bulks.  They are object-side geometry; numerical boundary traces and Hilbert
realizations are downstream realization surfaces.

Dependency order: compactification first, then boundary faces, then incidence
relations among faces.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
An indexed boundary system for an analytic bulk core.  It packages one
compactification, a family of boundary faces, and incidence data between faces.
-/
structure AnalyticBoundarySystem (X : AnalyticBulkCore) where
  compactification : AnalyticBulkCompactification X
  FaceIndex : Type
  face : FaceIndex → AnalyticBoundaryFace compactification
  IncidenceIndex : FaceIndex → FaceIndex → Type
  incidence :
    {i j : FaceIndex} →
      IncidenceIndex i j → AnalyticBoundaryIncidence (face i) (face j)

namespace AnalyticBoundarySystem

/-- The compactification underlying a boundary system. -/
def compactificationData {X : AnalyticBulkCore} (B : AnalyticBoundarySystem X) :
    AnalyticBulkCompactification X :=
  B.compactification

/-- The boundary face selected by an index. -/
def faceAt {X : AnalyticBulkCore} (B : AnalyticBoundarySystem X)
    (i : B.FaceIndex) : AnalyticBoundaryFace B.compactification :=
  B.face i

end AnalyticBoundarySystem

end AnalyticMotives
end LFunctions
end Boundary
