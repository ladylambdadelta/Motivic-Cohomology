import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Objects.Owner

/-!
# Values for presheaves on `ContourCor_Q`

This owner records the value assignment for presheaves on contour-admissible
analytic bulks.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A value assignment on contour-admissible analytic bulks. -/
structure ContourCorQPresheafValues where
  value : ContourCorQPresheafObject → Type

namespace ContourCorQPresheafValues

/-- The value assigned to one contour-admissible analytic bulk. -/
def valueAt (V : ContourCorQPresheafValues)
    (X : ContourCorQPresheafObject) : Type :=
  V.value X

end ContourCorQPresheafValues

end AnalyticMotives
end LFunctions
end Boundary
