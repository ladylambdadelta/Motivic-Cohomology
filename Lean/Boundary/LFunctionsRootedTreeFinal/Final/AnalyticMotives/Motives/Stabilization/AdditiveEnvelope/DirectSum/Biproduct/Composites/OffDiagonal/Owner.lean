import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Composites.Diagonal.Owner

/-!
# Off-diagonal entries of direct-sum biproduct composites

This file collapses the off-diagonal entries of the left-inclusion followed by
left-projection composite to zero.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- At the matching source summand index, the off-diagonal left-left summand is zero. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_sourceSummand_ne
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin left.length)
    (indices_ne : sourceIndex ≠ targetIndex) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right).entry
        sourceIndex
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex))
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        targetIndex) =
      0 :=
  Eq.trans
    (congrArg
      (fun tail =>
        TraceCorQHom.comp
          ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
            left
            right).entry
            sourceIndex
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex))
          tail)
      (Eq.trans
        (TraceAnalyticAdditiveCategory.leftDirectSumProjection_entry
          left
          right
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
          targetIndex)
        (TraceAnalyticAdditiveObject.leftDirectSumProjection_entry_ne_leftIndex
          left
          right
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
          targetIndex
          (fun index_eq =>
            indices_ne
              (TraceAnalyticAdditiveObject.leftDirectSumIndex_injective
                left
                right
                index_eq)))))
    (TraceCorQHom.std_comp_zero
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
        left
        right).entry
        sourceIndex
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)))

/-- Every off-diagonal summand in the left-left composite is zero. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_neEntrySummand
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin left.length)
    (indices_ne : sourceIndex ≠ targetIndex)
    (middleIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right).entry
        sourceIndex
        middleIndex)
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection left right).entry
        middleIndex
        targetIndex) =
      0 :=
  match Classical.decEq middleIndex
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex) with
  | isTrue middle_eq =>
      Eq.subst
        (motive := fun index =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
              left
              right).entry sourceIndex index)
            ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
              left
              right).entry index targetIndex) =
            0)
        (Eq.symm middle_eq)
        (TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_sourceSummand_ne
          left
          right
          sourceIndex
          targetIndex
          indices_ne)
  | isFalse middle_ne =>
      TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_neSummand
        left
        right
        sourceIndex
        targetIndex
        middleIndex
        middle_ne

/-- An off-diagonal entry of the left-left direct-sum composite is the zero identity entry. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_entry_ne
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin left.length)
    (indices_ne : sourceIndex ≠ targetIndex) :
    (TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection
      left
      right).entry sourceIndex targetIndex =
      (TraceAnalyticAdditiveCategory.id left).entry sourceIndex targetIndex :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_entry
      left
      right
      sourceIndex
      targetIndex)
    (Eq.trans
      (Finset.sum_eq_zero
        (fun middleIndex _membership =>
          TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_neEntrySummand
            left
            right
            sourceIndex
            targetIndex
            indices_ne
            middleIndex))
      (Eq.symm
        (TraceAnalyticAdditiveHom.id_entry_ne
          left
          sourceIndex
          targetIndex
          indices_ne)))

end AnalyticMotives
end LFunctions
end Boundary
