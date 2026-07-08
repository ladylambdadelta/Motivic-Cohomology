import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Reassembly.Full.Owner

/-!
# Entrywise direct-sum reassembly identity

This file transports the embedded-block reassembly identities along the
left/right split of arbitrary direct-sum indices.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The direct-sum reassembly endomorphism agrees entrywise with the identity. -/
theorem TraceAnalyticAdditiveCategory.directSumReassembly_entry_eq_id
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length) :
    (TraceAnalyticAdditiveCategory.directSumReassembly left right).entry
      sourceIndex
      targetIndex =
      (TraceAnalyticAdditiveCategory.id
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        sourceIndex
        targetIndex :=
  match Nat.lt_or_ge sourceIndex.val left.length with
  | Or.inl source_lt_left =>
      match Nat.lt_or_ge targetIndex.val left.length with
      | Or.inl target_lt_left =>
          let sourceLeftIndex :=
            TraceAnalyticAdditiveObject.leftIndexOfDirectSumIndex
              left
              right
              sourceIndex
              source_lt_left
          let targetLeftIndex :=
            TraceAnalyticAdditiveObject.leftIndexOfDirectSumIndex
              left
              right
              targetIndex
              target_lt_left
          let source_eq :=
            TraceAnalyticAdditiveObject.leftDirectSumIndex_leftIndexOf_eq
              left
              right
              sourceIndex
              source_lt_left
          let target_eq :=
            TraceAnalyticAdditiveObject.leftDirectSumIndex_leftIndexOf_eq
              left
              right
              targetIndex
              target_lt_left
          Eq.subst
            (motive := fun source =>
              (TraceAnalyticAdditiveCategory.directSumReassembly
                left
                right).entry source targetIndex =
                (TraceAnalyticAdditiveCategory.id
                  (TraceAnalyticAdditiveObject.directSum left right)).entry
                  source
                  targetIndex)
            source_eq
            (Eq.subst
              (motive := fun target =>
                (TraceAnalyticAdditiveCategory.directSumReassembly
                  left
                  right).entry
                  (TraceAnalyticAdditiveObject.leftDirectSumIndex
                    left
                    right
                    sourceLeftIndex)
                  target =
                  (TraceAnalyticAdditiveCategory.id
                    (TraceAnalyticAdditiveObject.directSum left right)).entry
                    (TraceAnalyticAdditiveObject.leftDirectSumIndex
                      left
                      right
                      sourceLeftIndex)
                    target)
              target_eq
              (TraceAnalyticAdditiveCategory.directSumReassembly_leftLeftEntry_eq_id
                left
                right
                sourceLeftIndex
                targetLeftIndex))
      | Or.inr target_ge_left =>
          let sourceLeftIndex :=
            TraceAnalyticAdditiveObject.leftIndexOfDirectSumIndex
              left
              right
              sourceIndex
              source_lt_left
          let targetRightIndex :=
            TraceAnalyticAdditiveObject.rightIndexOfDirectSumIndex
              left
              right
              targetIndex
              (Nat.not_lt_of_ge target_ge_left)
          let source_eq :=
            TraceAnalyticAdditiveObject.leftDirectSumIndex_leftIndexOf_eq
              left
              right
              sourceIndex
              source_lt_left
          let target_eq :=
            TraceAnalyticAdditiveObject.rightDirectSumIndex_rightIndexOf_eq
              left
              right
              targetIndex
              (Nat.not_lt_of_ge target_ge_left)
          Eq.subst
            (motive := fun source =>
              (TraceAnalyticAdditiveCategory.directSumReassembly
                left
                right).entry source targetIndex =
                (TraceAnalyticAdditiveCategory.id
                  (TraceAnalyticAdditiveObject.directSum left right)).entry
                  source
                  targetIndex)
            source_eq
            (Eq.subst
              (motive := fun target =>
                (TraceAnalyticAdditiveCategory.directSumReassembly
                  left
                  right).entry
                  (TraceAnalyticAdditiveObject.leftDirectSumIndex
                    left
                    right
                    sourceLeftIndex)
                  target =
                  (TraceAnalyticAdditiveCategory.id
                    (TraceAnalyticAdditiveObject.directSum left right)).entry
                    (TraceAnalyticAdditiveObject.leftDirectSumIndex
                      left
                      right
                      sourceLeftIndex)
                    target)
              target_eq
              (TraceAnalyticAdditiveCategory.directSumReassembly_leftRightEntry_eq_id
                left
                right
                sourceLeftIndex
                targetRightIndex))
  | Or.inr source_ge_left =>
      match Nat.lt_or_ge targetIndex.val left.length with
      | Or.inl target_lt_left =>
          let sourceRightIndex :=
            TraceAnalyticAdditiveObject.rightIndexOfDirectSumIndex
              left
              right
              sourceIndex
              (Nat.not_lt_of_ge source_ge_left)
          let targetLeftIndex :=
            TraceAnalyticAdditiveObject.leftIndexOfDirectSumIndex
              left
              right
              targetIndex
              target_lt_left
          let source_eq :=
            TraceAnalyticAdditiveObject.rightDirectSumIndex_rightIndexOf_eq
              left
              right
              sourceIndex
              (Nat.not_lt_of_ge source_ge_left)
          let target_eq :=
            TraceAnalyticAdditiveObject.leftDirectSumIndex_leftIndexOf_eq
              left
              right
              targetIndex
              target_lt_left
          Eq.subst
            (motive := fun source =>
              (TraceAnalyticAdditiveCategory.directSumReassembly
                left
                right).entry source targetIndex =
                (TraceAnalyticAdditiveCategory.id
                  (TraceAnalyticAdditiveObject.directSum left right)).entry
                  source
                  targetIndex)
            source_eq
            (Eq.subst
              (motive := fun target =>
                (TraceAnalyticAdditiveCategory.directSumReassembly
                  left
                  right).entry
                  (TraceAnalyticAdditiveObject.rightDirectSumIndex
                    left
                    right
                    sourceRightIndex)
                  target =
                  (TraceAnalyticAdditiveCategory.id
                    (TraceAnalyticAdditiveObject.directSum left right)).entry
                    (TraceAnalyticAdditiveObject.rightDirectSumIndex
                      left
                      right
                      sourceRightIndex)
                    target)
              target_eq
              (TraceAnalyticAdditiveCategory.directSumReassembly_rightLeftEntry_eq_id
                left
                right
                sourceRightIndex
                targetLeftIndex))
      | Or.inr target_ge_left =>
          let sourceRightIndex :=
            TraceAnalyticAdditiveObject.rightIndexOfDirectSumIndex
              left
              right
              sourceIndex
              (Nat.not_lt_of_ge source_ge_left)
          let targetRightIndex :=
            TraceAnalyticAdditiveObject.rightIndexOfDirectSumIndex
              left
              right
              targetIndex
              (Nat.not_lt_of_ge target_ge_left)
          let source_eq :=
            TraceAnalyticAdditiveObject.rightDirectSumIndex_rightIndexOf_eq
              left
              right
              sourceIndex
              (Nat.not_lt_of_ge source_ge_left)
          let target_eq :=
            TraceAnalyticAdditiveObject.rightDirectSumIndex_rightIndexOf_eq
              left
              right
              targetIndex
              (Nat.not_lt_of_ge target_ge_left)
          Eq.subst
            (motive := fun source =>
              (TraceAnalyticAdditiveCategory.directSumReassembly
                left
                right).entry source targetIndex =
                (TraceAnalyticAdditiveCategory.id
                  (TraceAnalyticAdditiveObject.directSum left right)).entry
                  source
                  targetIndex)
            source_eq
            (Eq.subst
              (motive := fun target =>
                (TraceAnalyticAdditiveCategory.directSumReassembly
                  left
                  right).entry
                  (TraceAnalyticAdditiveObject.rightDirectSumIndex
                    left
                    right
                    sourceRightIndex)
                  target =
                  (TraceAnalyticAdditiveCategory.id
                    (TraceAnalyticAdditiveObject.directSum left right)).entry
                    (TraceAnalyticAdditiveObject.rightDirectSumIndex
                      left
                      right
                      sourceRightIndex)
                    target)
              target_eq
              (TraceAnalyticAdditiveCategory.directSumReassembly_rightRightEntry_eq_id
                left
                right
                sourceRightIndex
                targetRightIndex))

/-- The direct-sum reassembly endomorphism is the identity. -/
theorem TraceAnalyticAdditiveCategory.directSumReassembly_eq_id
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.directSumReassembly left right =
      TraceAnalyticAdditiveCategory.id
        (TraceAnalyticAdditiveObject.directSum left right) :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceAnalyticAdditiveCategory.directSumReassembly_entry_eq_id
        left
        right
        sourceIndex
        targetIndex)

end AnalyticMotives
end LFunctions
end Boundary
