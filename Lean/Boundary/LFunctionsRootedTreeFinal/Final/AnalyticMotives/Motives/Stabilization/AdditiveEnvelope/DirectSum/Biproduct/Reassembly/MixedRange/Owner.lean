import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Reassembly.CrossRange.Owner

/-!
# Mixed-range zero entries of direct-sum reassembly projectors

This file proves that both direct-sum reassembly projectors vanish on the
off-block entries between the left and right summand ranges.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Every summand of the left projector on a left-to-right entry is zero. -/
theorem TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftRightSummand_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin left.length)
    (targetIndex : Fin right.length)
    (middleIndex : Fin left.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        middleIndex)
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right).entry
        middleIndex
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)) =
      0 :=
  Eq.trans
    (congrArg
      (fun tail =>
        TraceCorQHom.comp
          ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
            left
            right).entry
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
            middleIndex)
          tail)
      (Eq.trans
        (TraceAnalyticAdditiveCategory.leftDirectSumInclusion_entry
          left
          right
          middleIndex
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex))
        (TraceAnalyticAdditiveObject.leftDirectSumInclusion_entry_ne_leftIndex
          left
          right
          middleIndex
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)
          (TraceAnalyticAdditiveObject.rightDirectSumIndex_ne_leftDirectSumIndex
            left
            right
            targetIndex
            middleIndex))))
    (TraceCorQHom.std_comp_zero
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
        left
        right).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        middleIndex))

/-- Every left-to-right entry of the left projector is zero. -/
theorem TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftRightEntry_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin left.length)
    (targetIndex : Fin right.length) :
    (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion
      left
      right).entry
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) =
      (TraceAnalyticAdditiveCategory.zeroHom
        (TraceAnalyticAdditiveObject.directSum left right)
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_entry
      left
      right
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex))
    (Eq.trans
      (Finset.sum_eq_zero
        (fun middleIndex _membership =>
          TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftRightSummand_eq_zero
            left
            right
            sourceIndex
            targetIndex
            middleIndex))
      (Eq.symm
        (TraceAnalyticAdditiveCategory.zeroHom_entry
          (TraceAnalyticAdditiveObject.directSum left right)
          (TraceAnalyticAdditiveObject.directSum left right)
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex))))

/-- Every summand of the right projector on a left-to-right entry is zero. -/
theorem TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_leftRightSummand_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin left.length)
    (targetIndex : Fin right.length)
    (middleIndex : Fin right.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        middleIndex)
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right).entry
        middleIndex
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)) =
      0 :=
  Eq.trans
    (congrArg
      (fun head =>
        TraceCorQHom.comp
          head
          ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion
            left
            right).entry
            middleIndex
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.rightDirectSumProjection_entry
          left
          right
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
          middleIndex)
        (TraceAnalyticAdditiveObject.rightDirectSumProjection_entry_ne_rightIndex
          left
          right
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
          middleIndex
          (TraceAnalyticAdditiveObject.leftDirectSumIndex_ne_rightDirectSumIndex
            left
            right
            sourceIndex
            middleIndex))))
    (TraceCorQHom.std_zero_comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion
        left
        right).entry
        middleIndex
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)))

/-- Every left-to-right entry of the right projector is zero. -/
theorem TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_leftRightEntry_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin left.length)
    (targetIndex : Fin right.length) :
    (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion
      left
      right).entry
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) =
      (TraceAnalyticAdditiveCategory.zeroHom
        (TraceAnalyticAdditiveObject.directSum left right)
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_entry
      left
      right
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex))
    (Eq.trans
      (Finset.sum_eq_zero
        (fun middleIndex _membership =>
          TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_leftRightSummand_eq_zero
            left
            right
            sourceIndex
            targetIndex
            middleIndex))
      (Eq.symm
        (TraceAnalyticAdditiveCategory.zeroHom_entry
          (TraceAnalyticAdditiveObject.directSum left right)
          (TraceAnalyticAdditiveObject.directSum left right)
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex))))

/-- Every summand of the left projector on a right-to-left entry is zero. -/
theorem TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_rightLeftSummand_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin right.length)
    (targetIndex : Fin left.length)
    (middleIndex : Fin left.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        middleIndex)
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right).entry
        middleIndex
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)) =
      0 :=
  Eq.trans
    (congrArg
      (fun head =>
        TraceCorQHom.comp
          head
          ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
            left
            right).entry
            middleIndex
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.leftDirectSumProjection_entry
          left
          right
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
          middleIndex)
        (TraceAnalyticAdditiveObject.leftDirectSumProjection_entry_ne_leftIndex
          left
          right
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
          middleIndex
          (TraceAnalyticAdditiveObject.rightDirectSumIndex_ne_leftDirectSumIndex
            left
            right
            sourceIndex
            middleIndex))))
    (TraceCorQHom.std_zero_comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
        left
        right).entry
        middleIndex
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)))

/-- Every right-to-left entry of the left projector is zero. -/
theorem TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_rightLeftEntry_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin right.length)
    (targetIndex : Fin left.length) :
    (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion
      left
      right).entry
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) =
      (TraceAnalyticAdditiveCategory.zeroHom
        (TraceAnalyticAdditiveObject.directSum left right)
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_entry
      left
      right
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))
    (Eq.trans
      (Finset.sum_eq_zero
        (fun middleIndex _membership =>
          TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_rightLeftSummand_eq_zero
            left
            right
            sourceIndex
            targetIndex
            middleIndex))
      (Eq.symm
        (TraceAnalyticAdditiveCategory.zeroHom_entry
          (TraceAnalyticAdditiveObject.directSum left right)
          (TraceAnalyticAdditiveObject.directSum left right)
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))))

/-- Every summand of the right projector on a right-to-left entry is zero. -/
theorem TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightLeftSummand_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin right.length)
    (targetIndex : Fin left.length)
    (middleIndex : Fin right.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        middleIndex)
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right).entry
        middleIndex
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)) =
      0 :=
  Eq.trans
    (congrArg
      (fun tail =>
        TraceCorQHom.comp
          ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
            left
            right).entry
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
            middleIndex)
          tail)
      (Eq.trans
        (TraceAnalyticAdditiveCategory.rightDirectSumInclusion_entry
          left
          right
          middleIndex
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))
        (TraceAnalyticAdditiveObject.rightDirectSumInclusion_entry_ne_rightIndex
          left
          right
          middleIndex
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)
          (TraceAnalyticAdditiveObject.leftDirectSumIndex_ne_rightDirectSumIndex
            left
            right
            targetIndex
            middleIndex))))
    (TraceCorQHom.std_comp_zero
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
        left
        right).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        middleIndex))

/-- Every right-to-left entry of the right projector is zero. -/
theorem TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightLeftEntry_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin right.length)
    (targetIndex : Fin left.length) :
    (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion
      left
      right).entry
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) =
      (TraceAnalyticAdditiveCategory.zeroHom
        (TraceAnalyticAdditiveObject.directSum left right)
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_entry
      left
      right
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))
    (Eq.trans
      (Finset.sum_eq_zero
        (fun middleIndex _membership =>
          TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightLeftSummand_eq_zero
            left
            right
            sourceIndex
            targetIndex
            middleIndex))
      (Eq.symm
        (TraceAnalyticAdditiveCategory.zeroHom_entry
          (TraceAnalyticAdditiveObject.directSum left right)
          (TraceAnalyticAdditiveObject.directSum left right)
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))))

end AnalyticMotives
end LFunctions
end Boundary
