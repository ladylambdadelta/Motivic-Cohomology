import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.FormalSums.Reindexing.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.PrimeSupports.TransportImages.Owner

/-!
# Parent term images under formal-sum reindexing

This file records the term-level parent image computations needed for the
reindexing case of balanced-relation descent.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace AlgebraizedContourFormalSum

/-- Coefficients are transported contravariantly along the reindexing equivalence. -/
theorem reindex_coefficientAt
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (j : T.Index) :
    (A.reindex R).coefficientAt j =
      A.coefficientAt (R.indexEquiv.symm j) :=
  Eq.symm
    (Eq.trans
      (R.coefficient_eq (R.indexEquiv.symm j))
      (congrArg T.coefficient (R.indexEquiv.apply_symm_apply j)))

/-- Parent prime classes are transported contravariantly along reindexing. -/
theorem reindex_parentPrimeGeomAt
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (j : T.Index) :
    (A.reindex R).parentPrimeGeomAt j =
      A.parentPrimeGeomAt (R.indexEquiv.symm j) :=
  AlgebraizedContourPrimeSupport.transportCorrespondence_parentPrimeGeom
    (reindexing_correspondence_eq_target R j)
    (A.at (R.indexEquiv.symm j))

/-- Parent rational terms are transported by reindexing at the singleton level. -/
theorem reindex_parentRationalTermAt
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (j : T.Index) :
    (A.reindex R).parentRationalTermAt j =
      Finsupp.single
        (A.parentPrimeGeomAt (R.indexEquiv.symm j))
        (A.coefficientAt (R.indexEquiv.symm j)) :=
  Eq.trans
    (congrArg
      (fun q : Rat =>
        Finsupp.single
          ((A.reindex R).parentPrimeGeomAt j)
          q)
      (reindex_coefficientAt R A j))
      (congrArg
      (fun p : PrimeFiniteCorrespondenceGeom sourceBulk.scheme targetBulk.scheme =>
        Finsupp.single p (A.coefficientAt (R.indexEquiv.symm j)))
      (reindex_parentPrimeGeomAt R A j))

/-- Parent rational terms reindex to the corresponding old parent term. -/
theorem reindex_parentRationalTermAt_oldTerm
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (j : T.Index) :
    (A.reindex R).parentRationalTermAt j =
      A.parentRationalTermAt (R.indexEquiv.symm j) :=
  reindex_parentRationalTermAt R A j

/-- Reindexing an algebraized formal sum preserves its whole parent correspondence. -/
theorem reindex_parentRationalCorrespondence
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S) :
    (A.reindex R).parentRationalCorrespondence =
      A.parentRationalCorrespondence :=
  Fintype.sum_equiv
    R.indexEquiv.symm
    (fun j : T.Index => (A.reindex R).parentRationalTermAt j)
    (fun i : S.Index => A.parentRationalTermAt i)
    (fun j : T.Index => reindex_parentRationalTermAt_oldTerm R A j)

end AlgebraizedContourFormalSum

end

end AnalyticMotives
end LFunctions
end Boundary
