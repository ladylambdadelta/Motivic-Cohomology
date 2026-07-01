import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.PrimeSupports.Owner

/-!
# Transport of algebraized prime supports

This file owns the dependent transport of an algebraized parent prime support
along equality of raw contour correspondences.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

variable {G : PerfectAnalyticGround.{u}}

namespace AlgebraizedContourPrimeSupport

/-- Transport an algebraized prime support along equality of raw correspondences. -/
def transportCorrespondence
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C D : ContourAnalyticCorrespondence X Y}
    (h : C = D)
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    AlgebraizedContourPrimeSupport sourceBulk targetBulk D :=
  h ▸ A

/-- Transport along reflexivity does not change the algebraized prime support. -/
theorem transportCorrespondence_refl
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C : ContourAnalyticCorrespondence X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    transportCorrespondence rfl A = A :=
  rfl

end AlgebraizedContourPrimeSupport

end AnalyticMotives
end LFunctions
end Boundary
