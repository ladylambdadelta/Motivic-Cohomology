import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RationalHom.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.PrimeSupports.Transport.Owner

/-!
# Parent images under prime-support transport

This file records that transporting an algebraized prime support along equality
of raw contour correspondences preserves the represented parent prime class.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

variable {G : PerfectAnalyticGround.{u}}

namespace AlgebraizedContourPrimeSupport

/-- Transporting a prime support does not change its parent prime support. -/
theorem transportCorrespondence_parentPrime
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C D : ContourAnalyticCorrespondence X Y}
    (h : C = D)
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    (transportCorrespondence h A).parentPrime = A.parentPrime :=
  match h with
  | rfl => rfl

/-- Transporting a prime support does not change its parent geometric prime class. -/
theorem transportCorrespondence_parentPrimeGeom
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C D : ContourAnalyticCorrespondence X Y}
    (h : C = D)
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    (transportCorrespondence h A).parentPrimeGeom = A.parentPrimeGeom :=
  match h with
  | rfl => rfl

/-- Transporting a prime support does not change its parent rational correspondence. -/
theorem transportCorrespondence_parentRationalCorrespondence
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C D : ContourAnalyticCorrespondence X Y}
    (h : C = D)
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    (transportCorrespondence h A).parentRationalCorrespondence =
      A.parentRationalCorrespondence :=
  match h with
  | rfl => rfl

/-- Transporting a prime support does not change its parent `SmCorQ` hom. -/
theorem transportCorrespondence_parentSmCorQHom
    {X Y : ContourAdmissibleBulk}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {C D : ContourAnalyticCorrespondence X Y}
    (h : C = D)
    (category : SmCorQ (k := G.carrier))
    (A : AlgebraizedContourPrimeSupport sourceBulk targetBulk C) :
    (transportCorrespondence h A).parentSmCorQHom category =
      A.parentSmCorQHom category :=
  match h with
  | rfl => rfl

end AlgebraizedContourPrimeSupport

end AnalyticMotives
end LFunctions
end Boundary
