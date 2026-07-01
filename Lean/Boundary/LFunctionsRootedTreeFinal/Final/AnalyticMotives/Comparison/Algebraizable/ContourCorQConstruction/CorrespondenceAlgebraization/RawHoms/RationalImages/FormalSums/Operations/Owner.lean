import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RawHoms.RationalImages.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Reindexing.Owner

/-!
# Operation images for raw-hom rational formal sums

This file proves that the broad rational-image evaluator on formal contour
sums respects scaling and reindexing.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQRawHomRationalImageSystem

/-- Scaling a formal sum scales its broad parent rational image. -/
theorem formalSumImage_scale
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (q : Rat)
    (S : ContourCorQFormalSum X Y) :
    H.formalSumImage (ContourCorQFormalSum.scale q S) =
      q • H.formalSumImage S :=
  Eq.trans
    (Finset.sum_congr
      rfl
      (fun i _ =>
        smul_smul q (S.coeffAt i) (H.at (S.correspondenceAt i))))
    (Eq.symm Finset.smul_sum)

/-- Reindexing preserves each broad parent rational term along the index equivalence. -/
theorem reindexing_formalSumTerm
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (i : S.Index) :
    H.formalSumTerm S i =
      H.formalSumTerm T (R.indexEquiv i) :=
  congrArg₂
    (fun q image =>
      q • image)
    (R.coefficient_eq i)
    (H.at_eq_of_eq (R.correspondence_eq i))

/-- Reindexing preserves the broad parent rational image of a formal sum. -/
theorem formalSumImage_reindexing
    {X Y : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Y}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T) :
    H.formalSumImage S = H.formalSumImage T :=
  Fintype.sum_equiv
    R.indexEquiv
    (fun i : S.Index => H.formalSumTerm S i)
    (fun j : T.Index => H.formalSumTerm T j)
    (fun i : S.Index => H.reindexing_formalSumTerm R i)

end ContourCorQRawHomRationalImageSystem

end

end AnalyticMotives
end LFunctions
end Boundary
