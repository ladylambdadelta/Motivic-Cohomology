import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Reassembly.MixedRange.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Indices.Split.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Owner

/-!
# Full embedded-block direct-sum reassembly identity

This file combines the block projector calculations into the entrywise
reassembly identity on embedded left and right direct-sum coordinates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The direct-sum reassembly identity on a left-left embedded entry. -/
theorem TraceAnalyticAdditiveCategory.directSumReassembly_leftLeftEntry_eq_id
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin left.length) :
    (TraceAnalyticAdditiveCategory.directSumReassembly
      left
      right).entry
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) =
      (TraceAnalyticAdditiveCategory.id
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) :=
  match Classical.decEq sourceIndex targetIndex with
  | isTrue indices_eq =>
      Eq.subst
        (motive := fun target =>
          (TraceAnalyticAdditiveCategory.directSumReassembly
            left
            right).entry
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right target) =
            (TraceAnalyticAdditiveCategory.id
              (TraceAnalyticAdditiveObject.directSum left right)).entry
              (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
              (TraceAnalyticAdditiveObject.leftDirectSumIndex left right target))
        indices_eq
        (Eq.trans
          (TraceAnalyticAdditiveCategory.directSumReassembly_entry
            left
            right
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex))
          (Eq.trans
            (congrArg₂
              TraceCorQHom.add
              (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftEntry_self
                left
                right
                sourceIndex)
              (Eq.trans
                (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_leftRangeEntry_eq_zero
                  left
                  right
                  sourceIndex
                  sourceIndex)
                (TraceAnalyticAdditiveCategory.zeroHom_entry
                  (TraceAnalyticAdditiveObject.directSum left right)
                  (TraceAnalyticAdditiveObject.directSum left right)
                  (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
                  (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex))))
            (TraceCorQHom.add_zero
              ((TraceAnalyticAdditiveCategory.id
                (TraceAnalyticAdditiveObject.directSum left right)).entry
                (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
                (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)))))
  | isFalse indices_ne =>
      Eq.trans
        (TraceAnalyticAdditiveCategory.directSumReassembly_entry
          left
          right
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))
        (Eq.trans
          (congrArg₂
            TraceCorQHom.add
            (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftEntry_ne
              left
              right
              sourceIndex
              targetIndex
              indices_ne)
            (Eq.trans
              (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_leftRangeEntry_eq_zero
                left
                right
                sourceIndex
                targetIndex)
              (TraceAnalyticAdditiveCategory.zeroHom_entry
                (TraceAnalyticAdditiveObject.directSum left right)
                (TraceAnalyticAdditiveObject.directSum left right)
                (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
                (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))))
          (TraceCorQHom.add_zero
            ((TraceAnalyticAdditiveCategory.id
              (TraceAnalyticAdditiveObject.directSum left right)).entry
              (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
              (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))))

/-- The direct-sum reassembly identity on a right-right embedded entry. -/
theorem TraceAnalyticAdditiveCategory.directSumReassembly_rightRightEntry_eq_id
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin right.length) :
    (TraceAnalyticAdditiveCategory.directSumReassembly
      left
      right).entry
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) =
      (TraceAnalyticAdditiveCategory.id
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) :=
  match Classical.decEq sourceIndex targetIndex with
  | isTrue indices_eq =>
      Eq.subst
        (motive := fun target =>
          (TraceAnalyticAdditiveCategory.directSumReassembly
            left
            right).entry
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right target) =
            (TraceAnalyticAdditiveCategory.id
              (TraceAnalyticAdditiveObject.directSum left right)).entry
              (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
              (TraceAnalyticAdditiveObject.rightDirectSumIndex left right target))
        indices_eq
        (Eq.trans
          (TraceAnalyticAdditiveCategory.directSumReassembly_entry
            left
            right
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex))
          (Eq.trans
            (congrArg₂
              TraceCorQHom.add
              (Eq.trans
                (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_rightRangeEntry_eq_zero
                  left
                  right
                  sourceIndex
                  sourceIndex)
                (TraceAnalyticAdditiveCategory.zeroHom_entry
                  (TraceAnalyticAdditiveObject.directSum left right)
                  (TraceAnalyticAdditiveObject.directSum left right)
                  (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
                  (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)))
              (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightEntry_self
                left
                right
                sourceIndex))
            (TraceCorQHom.zero_add
              ((TraceAnalyticAdditiveCategory.id
                (TraceAnalyticAdditiveObject.directSum left right)).entry
                (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
                (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)))))
  | isFalse indices_ne =>
      Eq.trans
        (TraceAnalyticAdditiveCategory.directSumReassembly_entry
          left
          right
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex))
        (Eq.trans
          (congrArg₂
            TraceCorQHom.add
            (Eq.trans
              (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_rightRangeEntry_eq_zero
                left
                right
                sourceIndex
                targetIndex)
              (TraceAnalyticAdditiveCategory.zeroHom_entry
                (TraceAnalyticAdditiveObject.directSum left right)
                (TraceAnalyticAdditiveObject.directSum left right)
                (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
                (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)))
            (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightEntry_ne
              left
              right
              sourceIndex
              targetIndex
              indices_ne))
          (TraceCorQHom.zero_add
            ((TraceAnalyticAdditiveCategory.id
              (TraceAnalyticAdditiveObject.directSum left right)).entry
              (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
              (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex))))

/-- The direct-sum reassembly identity on a left-to-right embedded entry. -/
theorem TraceAnalyticAdditiveCategory.directSumReassembly_leftRightEntry_eq_id
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin left.length)
    (targetIndex : Fin right.length) :
    (TraceAnalyticAdditiveCategory.directSumReassembly
      left
      right).entry
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) =
      (TraceAnalyticAdditiveCategory.id
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.directSumReassembly_entry
      left
      right
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex))
    (Eq.trans
      (congrArg₂
        TraceCorQHom.add
        (Eq.trans
          (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftRightEntry_eq_zero
            left
            right
            sourceIndex
            targetIndex)
          (TraceAnalyticAdditiveCategory.zeroHom_entry
            (TraceAnalyticAdditiveObject.directSum left right)
            (TraceAnalyticAdditiveObject.directSum left right)
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)))
        (Eq.trans
          (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_leftRightEntry_eq_zero
            left
            right
            sourceIndex
            targetIndex)
          (TraceAnalyticAdditiveCategory.zeroHom_entry
            (TraceAnalyticAdditiveObject.directSum left right)
            (TraceAnalyticAdditiveObject.directSum left right)
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex))))
      (Eq.trans
        (TraceCorQHom.add_zero
          (TraceCorQHom.zero
            ((TraceAnalyticAdditiveObject.directSum left right).component
              (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex))
            ((TraceAnalyticAdditiveObject.directSum left right).component
              (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex))))
        (Eq.symm
          (TraceAnalyticAdditiveHom.id_entry_ne
            (TraceAnalyticAdditiveObject.directSum left right)
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)
            (TraceAnalyticAdditiveObject.leftDirectSumIndex_ne_rightDirectSumIndex
              left
              right
              sourceIndex
              targetIndex)))))

/-- The direct-sum reassembly identity on a right-to-left embedded entry. -/
theorem TraceAnalyticAdditiveCategory.directSumReassembly_rightLeftEntry_eq_id
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin right.length)
    (targetIndex : Fin left.length) :
    (TraceAnalyticAdditiveCategory.directSumReassembly
      left
      right).entry
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) =
      (TraceAnalyticAdditiveCategory.id
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.directSumReassembly_entry
      left
      right
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))
    (Eq.trans
      (congrArg₂
        TraceCorQHom.add
        (Eq.trans
          (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_rightLeftEntry_eq_zero
            left
            right
            sourceIndex
            targetIndex)
          (TraceAnalyticAdditiveCategory.zeroHom_entry
            (TraceAnalyticAdditiveObject.directSum left right)
            (TraceAnalyticAdditiveObject.directSum left right)
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)))
        (Eq.trans
          (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_rightLeftEntry_eq_zero
            left
            right
            sourceIndex
            targetIndex)
          (TraceAnalyticAdditiveCategory.zeroHom_entry
            (TraceAnalyticAdditiveObject.directSum left right)
            (TraceAnalyticAdditiveObject.directSum left right)
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))))
      (Eq.trans
        (TraceCorQHom.add_zero
          (TraceCorQHom.zero
            ((TraceAnalyticAdditiveObject.directSum left right).component
              (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex))
            ((TraceAnalyticAdditiveObject.directSum left right).component
              (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))))
        (Eq.symm
          (TraceAnalyticAdditiveHom.id_entry_ne
            (TraceAnalyticAdditiveObject.directSum left right)
            (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)
            (TraceAnalyticAdditiveObject.rightDirectSumIndex_ne_leftDirectSumIndex
              left
              right
              sourceIndex
              targetIndex)))))

end AnalyticMotives
end LFunctions
end Boundary
