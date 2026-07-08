import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Reassembly.LeftRange.Owner

/-!
# Right-range entries of the direct-sum reassembly projector

This file proves the right-summand matrix entries of the projection-then-
inclusion endomorphism of a binary direct sum.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The matching right-range summand of the right projector is the identity. -/
theorem TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightDiagonalSummand
    (left right : TraceAnalyticAdditiveCategoryObject)
    (index : Fin right.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)
        index)
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right).entry
        index
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)) =
      TraceCorQHom.id
        ((TraceAnalyticAdditiveObject.directSum left right).component
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)) :=
  Eq.trans
    (congrArg₂
      TraceCorQHom.comp
      (Eq.trans
        (TraceAnalyticAdditiveCategory.rightDirectSumProjection_entry
          left
          right
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)
          index)
        (TraceAnalyticAdditiveObject.rightDirectSumProjection_entry_rightIndex
          left
          right
          index))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.rightDirectSumInclusion_entry
          left
          right
          index
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index))
        (TraceAnalyticAdditiveObject.rightDirectSumInclusion_entry_rightIndex
          left
          right
          index)))
    (TraceAnalyticAdditiveHom.transportedId_comp_symm
      (TraceAnalyticAdditiveObject.rightDirectSumComponent_eq_target
        left
        right
        index))

/-- Away from the matching source summand, a right-range projector summand is zero. -/
theorem TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightNeSummand
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin right.length)
    (middleIndex : Fin right.length)
    (middle_ne : middleIndex ≠ sourceIndex) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
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
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
          middleIndex)
        (TraceAnalyticAdditiveObject.rightDirectSumProjection_entry_ne_rightIndex
          left
          right
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
          middleIndex
          (fun index_eq =>
            middle_ne
              (TraceAnalyticAdditiveObject.rightDirectSumIndex_injective
                left
                right
                (Eq.symm index_eq))))))
    (TraceCorQHom.std_zero_comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion
        left
        right).entry
        middleIndex
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)))

/-- At the matching source summand, an off-diagonal right-range projector summand is zero. -/
theorem TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightSourceSummand_ne
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin right.length)
    (indices_ne : sourceIndex ≠ targetIndex) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        sourceIndex)
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right).entry
        sourceIndex
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)) =
      0 :=
  Eq.trans
    (congrArg
      (fun tail =>
        TraceCorQHom.comp
          ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
            left
            right).entry
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
            sourceIndex)
          tail)
      (Eq.trans
        (TraceAnalyticAdditiveCategory.rightDirectSumInclusion_entry
          left
          right
          sourceIndex
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex))
        (TraceAnalyticAdditiveObject.rightDirectSumInclusion_entry_ne_rightIndex
          left
          right
          sourceIndex
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)
          (fun index_eq =>
            indices_ne
              (TraceAnalyticAdditiveObject.rightDirectSumIndex_injective
                left
                right
                (Eq.symm index_eq))))))
    (TraceCorQHom.std_comp_zero
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
        left
        right).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        sourceIndex))

/-- Every off-diagonal right-range summand of the right projector is zero. -/
theorem TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightNeEntrySummand
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin right.length)
    (indices_ne : sourceIndex ≠ targetIndex)
    (middleIndex : Fin right.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        middleIndex)
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right).entry
        middleIndex
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)) =
      0 :=
  match Classical.decEq middleIndex sourceIndex with
  | isTrue middle_eq =>
      Eq.subst
        (motive := fun index =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
              left
              right).entry
              (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
              index)
            ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion
              left
              right).entry
              index
              (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)) =
            0)
        (Eq.symm middle_eq)
        (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightSourceSummand_ne
          left
          right
          sourceIndex
          targetIndex
          indices_ne)
  | isFalse middle_ne =>
      TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightNeSummand
        left
        right
        sourceIndex
        targetIndex
        middleIndex
        middle_ne

/-- A right-range diagonal entry of the right projector is the direct-sum identity entry. -/
theorem TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightEntry_self
    (left right : TraceAnalyticAdditiveCategoryObject)
    (index : Fin right.length) :
    (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion
      left
      right).entry
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index) =
      (TraceAnalyticAdditiveCategory.id
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index) :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_entry
      left
      right
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index))
    (Eq.trans
      (Finset.sum_eq_single
        index
        (fun middleIndex _membership middle_ne =>
          TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightNeSummand
            left
            right
            index
            index
            middleIndex
            middle_ne)
        (fun index_not_mem =>
          False.elim
            (index_not_mem
              (Finset.mem_univ index))))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightDiagonalSummand
          left
          right
          index)
        (Eq.symm
          (TraceAnalyticAdditiveHom.id_entry_self
            (TraceAnalyticAdditiveObject.directSum left right)
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)))))

/-- A right-range off-diagonal entry of the right projector is the direct-sum zero identity entry. -/
theorem TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightEntry_ne
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin right.length)
    (indices_ne : sourceIndex ≠ targetIndex) :
    (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion
      left
      right).entry
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) =
      (TraceAnalyticAdditiveCategory.id
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_entry
      left
      right
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex))
    (Eq.trans
      (Finset.sum_eq_zero
        (fun middleIndex _membership =>
          TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightNeEntrySummand
            left
            right
            sourceIndex
            targetIndex
            indices_ne
            middleIndex))
      (Eq.symm
        (TraceAnalyticAdditiveHom.id_entry_ne
          (TraceAnalyticAdditiveObject.directSum left right)
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)
          (fun index_eq =>
            indices_ne
              (TraceAnalyticAdditiveObject.rightDirectSumIndex_injective
                left
                right
                index_eq)))))

end AnalyticMotives
end LFunctions
end Boundary
