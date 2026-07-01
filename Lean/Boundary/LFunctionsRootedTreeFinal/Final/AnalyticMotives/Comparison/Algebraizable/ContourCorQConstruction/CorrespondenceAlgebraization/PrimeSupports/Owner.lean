import Boundary.CorrespondenceSums
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceShadows.Contour.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.ParentMotives.SmoothAlgebraization.Owner

/-!
# Algebraized prime supports for contour correspondences

This file records the exact parent prime finite correspondence support attached
to an algebraizable contour-compatible analytic correspondence.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

variable {G : PerfectAnalyticGround.{u}}

/--
An algebraization of a contour correspondence as a parent prime finite
correspondence support.

The fields `sourceBulk` and `targetBulk` identify the analytic endpoints with
smooth schemes over the perfect ground.  The field `primeSupport` is the actual
parent support object used by `RationalFiniteCorrespondence`.
-/
structure AlgebraizedContourPrimeSupport
    {X Y : ContourAdmissibleBulk}
    (sourceBulk : SmoothAlgebraization G X)
    (targetBulk : SmoothAlgebraization G Y)
    (C : ContourAnalyticCorrespondence X Y) where
  primeSupport : PrimeFiniteCorrespondenceSupport
    sourceBulk.scheme targetBulk.scheme
  support_eq : primeSupport.support = C.algebraicSupport

namespace AlgebraizedContourPrimeSupport

/-- The parent prime support selected by an algebraized contour correspondence. -/
def parentPrime
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C : ContourAnalyticCorrespondence X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    PrimeFiniteCorrespondenceSupport sourceBulk.scheme targetBulk.scheme :=
  A.primeSupport

/-- The selected parent support has the contour correspondence's algebraic support. -/
theorem parentPrime_support_eq
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C : ContourAnalyticCorrespondence X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    A.parentPrime.support = C.algebraicSupport :=
  A.support_eq

/-- The selected parent source scheme realizes the analytic source shadow. -/
theorem source_scheme_eq_shadow
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C : ContourAnalyticCorrespondence X Y}
    (_A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    sourceBulk.scheme.scheme = X.algebraicShadow :=
  sourceBulk.scheme_eq_shadow

/-- The selected parent target scheme realizes the analytic target shadow. -/
theorem target_scheme_eq_shadow
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C : ContourAnalyticCorrespondence X Y}
    (_A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    targetBulk.scheme.scheme = Y.algebraicShadow :=
  targetBulk.scheme_eq_shadow

end AlgebraizedContourPrimeSupport

end AnalyticMotives
end LFunctions
end Boundary
