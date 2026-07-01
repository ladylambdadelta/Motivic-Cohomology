import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.BulkShadows.Owner
import Geometry.Schemes.Basic

/-!
# Smooth algebraizations of contour-admissible bulks

This file owns the bridge datum from an analytic contour bulk to the classical
smooth-scheme input expected by the parent effective-motive construction.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Ground-field data required by the parent smooth-motive constructors. -/
structure PerfectAnalyticGround where
  carrier : Type u
  field : Field carrier
  perfect : PerfectField carrier

namespace PerfectAnalyticGround

/-- The field structure carried by a perfect analytic ground. -/
instance fieldInstance (G : PerfectAnalyticGround) : Field G.carrier :=
  G.field

/-- The perfection structure carried by a perfect analytic ground. -/
instance perfectInstance (G : PerfectAnalyticGround) : PerfectField G.carrier :=
  G.perfect

end PerfectAnalyticGround

/--
A smooth algebraization of a contour-admissible analytic bulk.

The analytic bulk already carries a scheme-valued shadow.  This datum records
when that shadow is represented by a smooth scheme over the ground field.
-/
structure SmoothAlgebraization
    (G : PerfectAnalyticGround) (X : ContourAdmissibleBulk) where
  smoothScheme : Geometry.SmSchemeOver G.carrier
  shadow_eq : smoothScheme.scheme = X.algebraicShadow

namespace SmoothAlgebraization

/-- The smooth scheme over `k` attached to a smooth algebraization. -/
def scheme {G : PerfectAnalyticGround} {X : ContourAdmissibleBulk}
    (A : SmoothAlgebraization G X) :
    Geometry.SmSchemeOver G.carrier :=
  A.smoothScheme

/-- The scheme underlying the algebraization is the bulk shadow. -/
theorem scheme_eq_shadow {G : PerfectAnalyticGround}
    {X : ContourAdmissibleBulk}
    (A : SmoothAlgebraization G X) :
    A.scheme.scheme = X.algebraicShadow :=
  A.shadow_eq

end SmoothAlgebraization

end AnalyticMotives
end LFunctions
end Boundary
