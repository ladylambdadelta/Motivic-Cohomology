import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.ContourCorQ.Linearization.Composition.Reindexing.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RawHoms.RationalImages.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.Algebraizable.ContourCorQConstruction.CorrespondenceAlgebraization.RawHoms.RationalImages.FormalSums.Operations.Owner

/-!
# Formal composition images for broad raw-hom rational image systems

This file records the first direct computations of the broad rational image
evaluator on formally composed contour sums.
-/

universe u

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

noncomputable section

variable {G : PerfectAnalyticGround.{u}}

namespace ContourCorQRawHomRationalImageSystem

/-- Broad images of composed formal sums preserve left reindexing. -/
theorem formalSumImage_comp_reindex_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Z}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    {S T : ContourCorQFormalSum X Y}
    (R : ContourCorQFormalSumReindexing S T)
    (U : ContourCorQFormalSum Y Z) :
    H.formalSumImage (ContourCorQFormalSum.comp C S U) =
      H.formalSumImage (ContourCorQFormalSum.comp C T U) :=
  H.formalSumImage_reindexing
    (ContourCorQFormalSumReindexing.comp_reindex_left C R U)

/-- Broad images of composed formal sums preserve right reindexing. -/
theorem formalSumImage_comp_reindex_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Z}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (S : ContourCorQFormalSum X Y)
    {T U : ContourCorQFormalSum Y Z}
    (R : ContourCorQFormalSumReindexing T U) :
    H.formalSumImage (ContourCorQFormalSum.comp C S T) =
      H.formalSumImage (ContourCorQFormalSum.comp C S U) :=
  H.formalSumImage_reindexing
    (ContourCorQFormalSumReindexing.comp_reindex_right C S R)

/-- Composing with an empty formal sum on the left has zero broad image. -/
theorem formalSumImage_comp_zero_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Z}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (T : ContourCorQFormalSum Y Z) :
    H.formalSumImage
        (ContourCorQFormalSum.comp C (ContourCorQFormalSum.zero X Y) T) =
      0 :=
  Finset.sum_empty

/-- Composing with an empty formal sum on the right has zero broad image. -/
theorem formalSumImage_comp_zero_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Z}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (S : ContourCorQFormalSum X Y) :
    H.formalSumImage
        (ContourCorQFormalSum.comp C S (ContourCorQFormalSum.zero Y Z)) =
      0 :=
  Finset.sum_empty

/-- The broad image of a composed pair of one-term formal sums. -/
theorem formalSumImage_comp_term_term
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Z}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (q r : Rat)
    (f : ContourCorQRawHom X Y)
    (g : ContourCorQRawHom Y Z) :
    H.formalSumImage
        (ContourCorQFormalSum.comp C
          (ContourCorQFormalSum.term q f)
          (ContourCorQFormalSum.term r g)) =
      (q * r) • H.at (C.composeAt f g) :=
  Fintype.sum_unique
    (fun p : PUnit × PUnit =>
      H.formalSumTerm
        (ContourCorQFormalSum.comp C
          (ContourCorQFormalSum.term q f)
          (ContourCorQFormalSum.term r g))
        p)

/-- Broad formal-sum images are additive in the left composed formal sum. -/
theorem formalSumImage_comp_add_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Z}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (S₁ S₂ : ContourCorQFormalSum X Y)
    (T : ContourCorQFormalSum Y Z) :
    H.formalSumImage
        (ContourCorQFormalSum.comp C (ContourCorQFormalSum.add S₁ S₂) T) =
      H.formalSumImage (ContourCorQFormalSum.comp C S₁ T) +
        H.formalSumImage (ContourCorQFormalSum.comp C S₂ T) :=
  Eq.trans
    (H.formalSumImage_reindexing
      (ContourCorQFormalSumReindexing.comp_add_left C S₁ S₂ T))
    (H.formalSumImage_add
      (ContourCorQFormalSum.comp C S₁ T)
      (ContourCorQFormalSum.comp C S₂ T))

/-- Broad formal-sum images are additive in the right composed formal sum. -/
theorem formalSumImage_comp_add_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Z}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (S : ContourCorQFormalSum X Y)
    (T₁ T₂ : ContourCorQFormalSum Y Z) :
    H.formalSumImage
        (ContourCorQFormalSum.comp C S (ContourCorQFormalSum.add T₁ T₂)) =
      H.formalSumImage (ContourCorQFormalSum.comp C S T₁) +
        H.formalSumImage (ContourCorQFormalSum.comp C S T₂) :=
  Eq.trans
    (H.formalSumImage_reindexing
      (ContourCorQFormalSumReindexing.comp_add_right C S T₁ T₂))
    (H.formalSumImage_add
      (ContourCorQFormalSum.comp C S T₁)
      (ContourCorQFormalSum.comp C S T₂))

/-- Broad formal-sum images commute with left scalar multiplication before composition. -/
theorem formalSumImage_comp_scale_left
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Z}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (q : Rat)
    (S : ContourCorQFormalSum X Y)
    (T : ContourCorQFormalSum Y Z) :
    H.formalSumImage
        (ContourCorQFormalSum.comp C (ContourCorQFormalSum.scale q S) T) =
      q • H.formalSumImage (ContourCorQFormalSum.comp C S T) :=
  Eq.trans
    (H.formalSumImage_reindexing
      (ContourCorQFormalSumReindexing.comp_scale_left C q S T))
    (H.formalSumImage_scale q (ContourCorQFormalSum.comp C S T))

/-- Broad formal-sum images commute with right scalar multiplication before composition. -/
theorem formalSumImage_comp_scale_right
    (C : ContourCorrespondenceCalculus)
    {X Y Z : ContourCorQObject}
    {sourceBulk : SmoothAlgebraization G X}
    {targetBulk : SmoothAlgebraization G Z}
    (H : ContourCorQRawHomRationalImageSystem sourceBulk targetBulk)
    (q : Rat)
    (S : ContourCorQFormalSum X Y)
    (T : ContourCorQFormalSum Y Z) :
    H.formalSumImage
        (ContourCorQFormalSum.comp C S (ContourCorQFormalSum.scale q T)) =
      q • H.formalSumImage (ContourCorQFormalSum.comp C S T) :=
  Eq.trans
    (H.formalSumImage_reindexing
      (ContourCorQFormalSumReindexing.comp_scale_right C q S T))
    (H.formalSumImage_scale q (ContourCorQFormalSum.comp C S T))

end ContourCorQRawHomRationalImageSystem

end

end AnalyticMotives
end LFunctions
end Boundary
