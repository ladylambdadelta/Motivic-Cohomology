import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourAdmissible.Owner

/-!
# Algebraic shadows of contour bulks

This owner exposes the algebraic shadow already carried by a
contour-admissible bulk: its arithmetic base scheme.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The algebraic shadow scheme of a contour-admissible bulk. -/
def ContourAdmissibleBulk.algebraicShadow
    (X : ContourAdmissibleBulk) :
    ArithmeticBase :=
  X.core.base

/-- The analytic carrier attached to the algebraic shadow of a bulk. -/
def ContourAdmissibleBulk.shadowCarrier
    (X : ContourAdmissibleBulk) :
    AnalyticCarrier X.algebraicShadow :=
  X.core.carrier

/-- The algebraic shadow of a bulk is the base of its core. -/
theorem ContourAdmissibleBulk.algebraicShadow_eq_core_base
    (X : ContourAdmissibleBulk) :
    X.algebraicShadow = X.core.base :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
