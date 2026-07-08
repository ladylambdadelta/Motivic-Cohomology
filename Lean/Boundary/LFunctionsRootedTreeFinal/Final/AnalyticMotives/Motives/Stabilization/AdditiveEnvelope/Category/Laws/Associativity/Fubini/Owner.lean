import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Associativity.Expansion.Owner

/-!
# Fubini comparison for additive-envelope associativity

The two associated matrix-composition entries become the same double finite
sum after expanding outer summands, reordering the finite sums, and applying
pointwise trace associativity.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left outer entry sum expands to the left nested double sum. -/
theorem TraceAnalyticAdditiveCategory.assocLeftOuterEntrySum_eq_innerSums
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length) :
    TraceAnalyticAdditiveCategory.assocLeftOuterEntrySum
      left
      middle
      right
      sourceIndex
      targetIndex =
      Finset.univ.sum
        (fun thirdIndex =>
          TraceAnalyticAdditiveCategory.assocLeftInnerEntrySum
            left
            middle
            right
            sourceIndex
            targetIndex
            thirdIndex) :=
  Finset.sum_congr
    rfl
    (fun thirdIndex _membership =>
      TraceAnalyticAdditiveCategory.assocLeftOuterSummand_eq_innerEntrySum
        left
        middle
        right
        sourceIndex
        targetIndex
        thirdIndex)

/-- The right outer entry sum expands to the right nested double sum. -/
theorem TraceAnalyticAdditiveCategory.assocRightOuterEntrySum_eq_innerSums
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length) :
    TraceAnalyticAdditiveCategory.assocRightOuterEntrySum
      left
      middle
      right
      sourceIndex
      targetIndex =
      Finset.univ.sum
        (fun secondIndex =>
          TraceAnalyticAdditiveCategory.assocRightInnerEntrySum
            left
            middle
            right
            sourceIndex
            targetIndex
            secondIndex) :=
  Finset.sum_congr
    rfl
    (fun secondIndex _membership =>
      TraceAnalyticAdditiveCategory.assocRightOuterSummand_eq_innerEntrySum
        left
        middle
        right
        sourceIndex
        targetIndex
        secondIndex)

/-- Reordering the left nested sum yields the right-associated nested sum. -/
theorem TraceAnalyticAdditiveCategory.assocLeftInnerSums_eq_rightInnerSums
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length) :
    Finset.univ.sum
      (fun thirdIndex =>
        TraceAnalyticAdditiveCategory.assocLeftInnerEntrySum
          left
          middle
          right
          sourceIndex
          targetIndex
          thirdIndex) =
      Finset.univ.sum
        (fun secondIndex =>
          TraceAnalyticAdditiveCategory.assocRightInnerEntrySum
            left
            middle
            right
            sourceIndex
            targetIndex
            secondIndex) :=
  Eq.trans
    (Finset.sum_congr
      rfl
      (fun thirdIndex _membership =>
        TraceAnalyticAdditiveCategory.assocLeftInnerEntrySum_eq_rightSummandSum
          left
          middle
          right
          sourceIndex
          targetIndex
          thirdIndex))
    (Eq.trans
      Finset.sum_comm
      (Finset.sum_congr
        rfl
        (fun secondIndex _membership =>
          Eq.symm
            (TraceAnalyticAdditiveCategory.assocRightInnerEntrySum_eq_leftSummandSum
              left
              middle
              right
              sourceIndex
              targetIndex
              secondIndex))))

/-- The two associativity outer entry sums are equal. -/
theorem TraceAnalyticAdditiveCategory.assocLeftOuterEntrySum_eq_rightOuterEntrySum
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length) :
    TraceAnalyticAdditiveCategory.assocLeftOuterEntrySum
      left
      middle
      right
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.assocRightOuterEntrySum
        left
        middle
        right
        sourceIndex
        targetIndex :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.assocLeftOuterEntrySum_eq_innerSums
      left
      middle
      right
      sourceIndex
      targetIndex)
    (Eq.trans
      (TraceAnalyticAdditiveCategory.assocLeftInnerSums_eq_rightInnerSums
        left
        middle
        right
        sourceIndex
        targetIndex)
      (Eq.symm
        (TraceAnalyticAdditiveCategory.assocRightOuterEntrySum_eq_innerSums
          left
          middle
          right
          sourceIndex
          targetIndex)))

end AnalyticMotives
end LFunctions
end Boundary
