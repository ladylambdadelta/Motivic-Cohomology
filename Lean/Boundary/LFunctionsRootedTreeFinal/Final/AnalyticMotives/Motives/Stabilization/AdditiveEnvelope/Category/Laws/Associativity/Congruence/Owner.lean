import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Associativity.Summands.Owner

/-!
# Finite-sum congruence for additive-envelope associativity

The pointwise trace associativity law lifts to equality of the inner finite
sums at each fixed outer intermediate index.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- At a fixed third index, the left inner sum is the sum of right inner summands. -/
theorem TraceAnalyticAdditiveCategory.assocLeftInnerEntrySum_eq_rightSummandSum
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length)
    (thirdIndex : Fin third.length) :
    TraceAnalyticAdditiveCategory.assocLeftInnerEntrySum
      left
      middle
      right
      sourceIndex
      targetIndex
      thirdIndex =
      Finset.univ.sum
        (fun secondIndex =>
          TraceAnalyticAdditiveCategory.assocRightInnerSummand
            left
            middle
            right
            sourceIndex
            targetIndex
            secondIndex
            thirdIndex) :=
  Finset.sum_congr
    rfl
    (fun secondIndex _membership =>
      TraceAnalyticAdditiveCategory.assocLeftInnerSummand_eq_rightInnerSummand
        left
        middle
        right
        sourceIndex
        targetIndex
        secondIndex
        thirdIndex)

/-- At a fixed second index, the right inner sum is the sum of left inner summands. -/
theorem TraceAnalyticAdditiveCategory.assocRightInnerEntrySum_eq_leftSummandSum
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length)
    (secondIndex : Fin second.length) :
    TraceAnalyticAdditiveCategory.assocRightInnerEntrySum
      left
      middle
      right
      sourceIndex
      targetIndex
      secondIndex =
      Finset.univ.sum
        (fun thirdIndex =>
          TraceAnalyticAdditiveCategory.assocLeftInnerSummand
            left
            middle
            right
            sourceIndex
            targetIndex
            thirdIndex
            secondIndex) :=
  Finset.sum_congr
    rfl
    (fun thirdIndex _membership =>
      Eq.symm
        (TraceAnalyticAdditiveCategory.assocLeftInnerSummand_eq_rightInnerSummand
          left
          middle
          right
          sourceIndex
          targetIndex
          secondIndex
          thirdIndex))

end AnalyticMotives
end LFunctions
end Boundary
