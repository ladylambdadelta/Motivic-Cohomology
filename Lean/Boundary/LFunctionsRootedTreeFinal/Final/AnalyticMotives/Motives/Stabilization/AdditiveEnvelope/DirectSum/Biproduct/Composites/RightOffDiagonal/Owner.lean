import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Composites.RightDiagonal.Owner

/-!
# Off-diagonal entries of the right-right direct-sum composite

This file collapses the off-diagonal entries of the right-inclusion followed by
right-projection composite to zero.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- At the matching source summand index, the off-diagonal right-right summand is zero. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_sourceSummand_ne
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin right.length)
    (indices_ne : sourceIndex ≠ targetIndex) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right).entry
        sourceIndex
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex))
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        targetIndex) =
      0 :=
  Eq.trans
    (congrArg
      (fun tail =>
        TraceCorQHom.comp
          ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion
            left
            right).entry
            sourceIndex
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex))
          tail)
      (Eq.trans
        (TraceAnalyticAdditiveCategory.rightDirectSumProjection_entry
          left
          right
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
          targetIndex)
        (TraceAnalyticAdditiveObject.rightDirectSumProjection_entry_ne_rightIndex
          left
          right
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
          targetIndex
          (fun index_eq =>
            indices_ne
              (TraceAnalyticAdditiveObject.rightDirectSumIndex_injective
                left
                right
                index_eq)))))
    (TraceCorQHom.std_comp_zero
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion
        left
        right).entry
        sourceIndex
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)))

/-- Every off-diagonal summand in the right-right composite is zero. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_neEntrySummand
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin right.length)
    (indices_ne : sourceIndex ≠ targetIndex)
    (middleIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right).entry
        sourceIndex
        middleIndex)
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection left right).entry
        middleIndex
        targetIndex) =
      0 :=
  match Classical.decEq middleIndex
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex) with
  | isTrue middle_eq =>
      Eq.subst
        (motive := fun index =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion
              left
              right).entry sourceIndex index)
            ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
              left
              right).entry index targetIndex) =
            0)
        (Eq.symm middle_eq)
        (TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_sourceSummand_ne
          left
          right
          sourceIndex
          targetIndex
          indices_ne)
  | isFalse middle_ne =>
      TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_neSummand
        left
        right
        sourceIndex
        targetIndex
        middleIndex
        middle_ne

/-- An off-diagonal entry of the right-right direct-sum composite is the zero identity entry. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_entry_ne
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin right.length)
    (indices_ne : sourceIndex ≠ targetIndex) :
    (TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection
      left
      right).entry sourceIndex targetIndex =
      (TraceAnalyticAdditiveCategory.id right).entry sourceIndex targetIndex :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_entry
      left
      right
      sourceIndex
      targetIndex)
    (Eq.trans
      (Finset.sum_eq_zero
        (fun middleIndex _membership =>
          TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_neEntrySummand
            left
            right
            sourceIndex
            targetIndex
            indices_ne
            middleIndex))
      (Eq.symm
        (TraceAnalyticAdditiveHom.id_entry_ne
          right
          sourceIndex
          targetIndex
          indices_ne)))

end AnalyticMotives
end LFunctions
end Boundary
