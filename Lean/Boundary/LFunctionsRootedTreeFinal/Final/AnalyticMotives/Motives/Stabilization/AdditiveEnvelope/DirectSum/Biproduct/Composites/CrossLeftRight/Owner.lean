import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Ext.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Composites.RightFull.Owner

/-!
# Left-to-right cross direct-sum composite

The left inclusion followed by the right projection is the zero matrix.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Every summand in the left-to-right cross composite is zero. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_rightProjection_summand_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin left.length)
    (targetIndex : Fin right.length)
    (middleIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right).entry
        sourceIndex
        middleIndex)
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection left right).entry
        middleIndex
        targetIndex) =
      0 :=
  match Classical.decEq middleIndex
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex) with
  | isTrue middle_eq =>
      Eq.trans
        (congrArg
          (fun tail =>
            TraceCorQHom.comp
              ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
                left
                right).entry sourceIndex middleIndex)
              tail)
          (Eq.trans
            (TraceAnalyticAdditiveCategory.rightDirectSumProjection_entry
              left
              right
              middleIndex
              targetIndex)
            (TraceAnalyticAdditiveObject.rightDirectSumProjection_entry_ne_rightIndex
              left
              right
              middleIndex
              targetIndex
              (fun middle_eq_right =>
                TraceAnalyticAdditiveObject.leftDirectSumIndex_ne_rightDirectSumIndex
                  left
                  right
                  sourceIndex
                  targetIndex
                  (Eq.trans middle_eq middle_eq_right)))))
        (TraceCorQHom.std_comp_zero
          ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
            left
            right).entry sourceIndex middleIndex))
  | isFalse middle_ne =>
      Eq.trans
        (congrArg
          (fun head =>
            TraceCorQHom.comp
              head
              ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
                left
                right).entry middleIndex targetIndex))
          (Eq.trans
            (TraceAnalyticAdditiveCategory.leftDirectSumInclusion_entry
              left
              right
              sourceIndex
              middleIndex)
            (TraceAnalyticAdditiveObject.leftDirectSumInclusion_entry_ne_leftIndex
              left
              right
              sourceIndex
              middleIndex
              middle_ne)))
        (TraceCorQHom.std_zero_comp
          ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
            left
            right).entry middleIndex targetIndex))

/-- Every entry in the left-to-right cross composite is zero. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_rightProjection_entry_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin left.length)
    (targetIndex : Fin right.length) :
    (TraceAnalyticAdditiveCategory.leftInclusion_comp_rightProjection
      left
      right).entry sourceIndex targetIndex =
      (TraceAnalyticAdditiveCategory.zeroHom left right).entry
        sourceIndex
        targetIndex :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.leftInclusion_comp_rightProjection_entry
      left
      right
      sourceIndex
      targetIndex)
    (Eq.trans
      (Finset.sum_eq_zero
        (fun middleIndex _membership =>
          TraceAnalyticAdditiveCategory.leftInclusion_comp_rightProjection_summand_eq_zero
            left
            right
            sourceIndex
            targetIndex
            middleIndex))
      (Eq.symm
        (TraceAnalyticAdditiveCategory.zeroHom_entry
          left
          right
          sourceIndex
          targetIndex)))

/-- The left inclusion followed by the right projection is zero. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_rightProjection_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.leftInclusion_comp_rightProjection left right =
      TraceAnalyticAdditiveCategory.zeroHom left right :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceAnalyticAdditiveCategory.leftInclusion_comp_rightProjection_entry_eq_zero
        left
        right
        sourceIndex
        targetIndex)

end AnalyticMotives
end LFunctions
end Boundary
