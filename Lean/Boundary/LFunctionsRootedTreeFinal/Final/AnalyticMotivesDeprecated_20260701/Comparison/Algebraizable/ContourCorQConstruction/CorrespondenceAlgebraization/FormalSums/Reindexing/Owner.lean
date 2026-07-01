import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Reindexing.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.PrimeSupports.Transport.Owner

/-!
# Reindexing algebraized contour formal sums

This file transports termwise algebraization data across a formal-sum
reindexing.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace AlgebraizedContourFormalSum

/-- The raw-correspondence equality used to transport an algebraized summand. -/
theorem reindexing_correspondence_eq_target
    {X Y : ContourCorQObject}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (j : T.Index) :
    S.correspondenceAt (R.indexEquiv.symm j) = T.correspondenceAt j :=
  Eq.trans
    (R.correspondence_eq (R.indexEquiv.symm j))
    (congrArg T.correspondence (R.indexEquiv.apply_symm_apply j))

/-- Transport an algebraized formal sum along a reindexing of finite summands. -/
def reindex
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S) :
    AlgebraizedContourFormalSum sourceBulk targetBulk T where
  termAlgebraization := fun j =>
    AlgebraizedContourPrimeSupport.transportCorrespondence
      (reindexing_correspondence_eq_target R j)
      (A.at (R.indexEquiv.symm j))

/-- Reindexing by reflexivity preserves the selected algebraization at each index. -/
theorem reindex_refl_at
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    {S : ContourCorQFormalSum X Y}
    (A : AlgebraizedContourFormalSum sourceBulk targetBulk S)
    (i : S.Index) :
    (AlgebraizedContourFormalSum.reindex
      (ContourCorQFormalSumReindexing.refl S) A).at i = A.at i :=
  rfl

end AlgebraizedContourFormalSum

end

end AnalyticMotives
end LFunctions
end Boundary
