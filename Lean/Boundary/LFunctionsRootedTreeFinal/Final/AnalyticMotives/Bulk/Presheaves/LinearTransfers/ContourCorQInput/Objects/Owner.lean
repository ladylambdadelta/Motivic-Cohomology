import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.TransferReady.Owner

/-!
# Objects for the `ContourCor_Q` presheaf input

This owner exposes the object type consumed by presheaves with contour
transfers: contour-admissible analytic bulks.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Objects of the transfer input category for contour presheaves. -/
abbrev ContourCorQPresheafObject :=
  ContourCorQObject

/-- Interpret a presheaf-input object as a contour-admissible analytic bulk. -/
def ContourCorQPresheafObject.toBulk
    (X : ContourCorQPresheafObject) :
    ContourAdmissibleBulk :=
  X

end AnalyticMotives
end LFunctions
end Boundary
