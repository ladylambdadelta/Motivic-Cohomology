import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.CompositionLinearity.FiniteSums.Owner

/-!
# Finite-sum congruence for composition-linearity entries

This file lifts pointwise summand-family comparisons to comparisons of their
finite sums over the middle index.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-zero source sum equals the zero-target summand-family sum. -/
theorem TraceAnalyticAdditiveCategory.zeroLeftCompositionEntrySum_eq_target
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.zeroLeftCompositionEntrySum
      right
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.zeroCompositionTargetEntrySum
        (middle := middle)
        sourceIndex
        targetIndex :=
  Finset.sum_congr
    rfl
    (fun middleIndex _membership =>
      TraceAnalyticAdditiveCategory.zeroLeftCompositionSummand_eq_target
        right
        sourceIndex
        targetIndex
        middleIndex)

/-- The right-zero source sum equals the zero-target summand-family sum. -/
theorem TraceAnalyticAdditiveCategory.zeroRightCompositionEntrySum_eq_target
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.zeroRightCompositionEntrySum
      left
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.zeroCompositionTargetEntrySum
        (middle := middle)
        sourceIndex
        targetIndex :=
  Finset.sum_congr
    rfl
    (fun middleIndex _membership =>
      TraceAnalyticAdditiveCategory.zeroRightCompositionSummand_eq_target
        left
        sourceIndex
        targetIndex
        middleIndex)

/-- The left-additivity source sum equals the left-additivity expansion sum. -/
theorem TraceAnalyticAdditiveCategory.addLeftCompositionEntrySum_eq_expansion
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.addLeftCompositionEntrySum
      left
      right
      tail
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.leftCompositionAddExpansionEntrySum
        left
        right
        tail
        sourceIndex
        targetIndex :=
  Finset.sum_congr
    rfl
    (fun middleIndex _membership =>
      TraceAnalyticAdditiveCategory.addLeftCompositionSummand_eq_expansion
        left
        right
        tail
        sourceIndex
        targetIndex
        middleIndex)

/-- The right-additivity source sum equals the right-additivity expansion sum. -/
theorem TraceAnalyticAdditiveCategory.addRightCompositionEntrySum_eq_expansion
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.addRightCompositionEntrySum
      head
      left
      right
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.rightCompositionAddExpansionEntrySum
        head
        left
        right
        sourceIndex
        targetIndex :=
  Finset.sum_congr
    rfl
    (fun middleIndex _membership =>
      TraceAnalyticAdditiveCategory.addRightCompositionSummand_eq_expansion
        head
        left
        right
        sourceIndex
        targetIndex
        middleIndex)

/-- The left scalar-linearity source sum equals the scalar expansion sum. -/
theorem TraceAnalyticAdditiveCategory.smulLeftCompositionEntrySum_eq_expansion
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.smulLeftCompositionEntrySum
      coefficient
      left
      right
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.compositionSmulExpansionEntrySum
        coefficient
        left
        right
        sourceIndex
        targetIndex :=
  Finset.sum_congr
    rfl
    (fun middleIndex _membership =>
      TraceAnalyticAdditiveCategory.smulLeftCompositionSummand_eq_expansion
        coefficient
        left
        right
        sourceIndex
        targetIndex
        middleIndex)

/-- The right scalar-linearity source sum equals the scalar expansion sum. -/
theorem TraceAnalyticAdditiveCategory.smulRightCompositionEntrySum_eq_expansion
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.smulRightCompositionEntrySum
      coefficient
      left
      right
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.compositionSmulExpansionEntrySum
        coefficient
        left
        right
        sourceIndex
        targetIndex :=
  Finset.sum_congr
    rfl
    (fun middleIndex _membership =>
      TraceAnalyticAdditiveCategory.smulRightCompositionSummand_eq_expansion
        coefficient
        left
        right
        sourceIndex
        targetIndex
        middleIndex)

end AnalyticMotives
end LFunctions
end Boundary
