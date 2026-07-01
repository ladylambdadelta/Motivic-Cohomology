import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RawHoms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.FormalSums.Reindexing.Owner

/-!
# Raw-hom algebraization systems and reindexing

This file proves that a reindexing of formal contour sums preserves the parent
rational finite correspondence obtained from a raw-hom algebraization system.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQRawHomAlgebraizationSystem

/-- Reindexing preserves the parent rational term attached by a raw-hom system. -/
theorem reindexing_parentRationalTermAt
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (i : S.Index) :
    (H.formalSum S).parentRationalTermAt i =
      (H.formalSum T).parentRationalTermAt (R.indexEquiv i) :=
  Eq.trans
    (congrArg
      (fun p : PrimeFiniteCorrespondenceGeom sourceBulk.scheme targetBulk.scheme =>
        Finsupp.single p ((H.formalSum S).coefficientAt i))
      (Eq.trans
        (Eq.symm
          (AlgebraizedContourPrimeSupport.transportCorrespondence_parentPrimeGeom
            (R.correspondence_eq i)
            (H.at (S.correspondenceAt i))))
        (H.parentPrimeGeom_eq_of_eq (R.correspondence_eq i))))
    (congrArg
      (fun q : Rat =>
        Finsupp.single
          ((H.formalSum T).parentPrimeGeomAt (R.indexEquiv i))
          q)
      (R.coefficient_eq i))

/-- Reindexing preserves the whole parent rational correspondence attached by a raw-hom system. -/
theorem reindexing_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomAlgebraizationSystem sourceBulk targetBulk)
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T) :
    (H.formalSum S).parentRationalCorrespondence =
      (H.formalSum T).parentRationalCorrespondence :=
  Fintype.sum_equiv
    R.indexEquiv
    (fun i : S.Index => (H.formalSum S).parentRationalTermAt i)
    (fun j : T.Index => (H.formalSum T).parentRationalTermAt j)
    (fun i : S.Index => H.reindexing_parentRationalTermAt R i)

end ContourCorQRawHomAlgebraizationSystem

end

end AnalyticMotives
end LFunctions
end Boundary
