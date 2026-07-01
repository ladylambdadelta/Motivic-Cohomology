import Boundary.RationalCompositionCategory
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.PrimeSupports.Owner

/-!
# Rational parent correspondences from algebraized contour correspondences

This file turns an algebraized contour prime support into the concrete parent
`SmCorQ` hom type: a rational finite correspondence.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace AlgebraizedContourPrimeSupport

/-- The geometric prime correspondence class represented by the algebraized support. -/
def parentPrimeGeom
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C : ContourAnalyticCorrespondence X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    PrimeFiniteCorrespondenceGeom sourceBulk.scheme targetBulk.scheme :=
  PrimeFiniteCorrespondenceGeom.ofRepresented A.parentPrime

/-- The rational finite correspondence represented by one algebraized contour support. -/
def parentRationalCorrespondence
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C : ContourAnalyticCorrespondence X Y}
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    RationalFiniteCorrespondence sourceBulk.scheme targetBulk.scheme :=
  Finsupp.single A.parentPrimeGeom 1

/-- The parent `SmCorQ` hom represented by one algebraized contour support. -/
def parentSmCorQHom
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C : ContourAnalyticCorrespondence X Y}
    (_category : SmCorQ (k := G.carrier))
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    SmCorQ.Hom _category sourceBulk.scheme targetBulk.scheme :=
  A.parentRationalCorrespondence

/-- The parent `SmCorQ` hom is the singleton rational finite correspondence. -/
theorem parentSmCorQHom_eq_single
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C : ContourAnalyticCorrespondence X Y}
    (category : SmCorQ (k := G.carrier))
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    A.parentSmCorQHom category =
      Finsupp.single A.parentPrimeGeom 1 :=
  rfl

end AlgebraizedContourPrimeSupport

end

end AnalyticMotives
end LFunctions
end Boundary
