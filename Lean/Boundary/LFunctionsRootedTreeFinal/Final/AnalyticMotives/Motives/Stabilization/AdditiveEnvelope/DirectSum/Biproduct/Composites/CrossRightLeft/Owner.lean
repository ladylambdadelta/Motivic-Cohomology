import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Composites.CrossLeftRight.Owner

/-!
# Right-to-left cross direct-sum composite

The right inclusion followed by the left projection is the zero matrix.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Every summand in the right-to-left cross composite is zero. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_leftProjection_summand_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin right.length)
    (targetIndex : Fin left.length)
    (middleIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right).entry
        sourceIndex
        middleIndex)
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection left right).entry
        middleIndex
        targetIndex) =
      0 :=
  match Classical.decEq middleIndex
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex) with
  | isTrue middle_eq =>
      Eq.trans
        (congrArg
          (fun tail =>
            TraceCorQHom.comp
              ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion
                left
                right).entry sourceIndex middleIndex)
              tail)
          (Eq.trans
            (TraceAnalyticAdditiveCategory.leftDirectSumProjection_entry
              left
              right
              middleIndex
              targetIndex)
            (TraceAnalyticAdditiveObject.leftDirectSumProjection_entry_ne_leftIndex
              left
              right
              middleIndex
              targetIndex
              (fun middle_eq_left =>
                TraceAnalyticAdditiveObject.rightDirectSumIndex_ne_leftDirectSumIndex
                  left
                  right
                  sourceIndex
                  targetIndex
                  (Eq.trans middle_eq middle_eq_left)))))
        (TraceCorQHom.std_comp_zero
          ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion
            left
            right).entry sourceIndex middleIndex))
  | isFalse middle_ne =>
      Eq.trans
        (congrArg
          (fun head =>
            TraceCorQHom.comp
              head
              ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
                left
                right).entry middleIndex targetIndex))
          (Eq.trans
            (TraceAnalyticAdditiveCategory.rightDirectSumInclusion_entry
              left
              right
              sourceIndex
              middleIndex)
            (TraceAnalyticAdditiveObject.rightDirectSumInclusion_entry_ne_rightIndex
              left
              right
              sourceIndex
              middleIndex
              middle_ne)))
        (TraceCorQHom.std_zero_comp
          ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
            left
            right).entry middleIndex targetIndex))

/-- Every entry in the right-to-left cross composite is zero. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_leftProjection_entry_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin right.length)
    (targetIndex : Fin left.length) :
    (TraceAnalyticAdditiveCategory.rightInclusion_comp_leftProjection
      left
      right).entry sourceIndex targetIndex =
      (TraceAnalyticAdditiveCategory.zeroHom right left).entry
        sourceIndex
        targetIndex :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.rightInclusion_comp_leftProjection_entry
      left
      right
      sourceIndex
      targetIndex)
    (Eq.trans
      (Finset.sum_eq_zero
        (fun middleIndex _membership =>
          TraceAnalyticAdditiveCategory.rightInclusion_comp_leftProjection_summand_eq_zero
            left
            right
            sourceIndex
            targetIndex
            middleIndex))
      (Eq.symm
        (TraceAnalyticAdditiveCategory.zeroHom_entry
          right
          left
          sourceIndex
          targetIndex)))

/-- The right inclusion followed by the left projection is zero. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_leftProjection_eq_zero
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.rightInclusion_comp_leftProjection left right =
      TraceAnalyticAdditiveCategory.zeroHom right left :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceAnalyticAdditiveCategory.rightInclusion_comp_leftProjection_entry_eq_zero
        left
        right
        sourceIndex
        targetIndex)

end AnalyticMotives
end LFunctions
end Boundary
