import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.FiniteSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Associativity.Congruence.Owner

/-!
# Finite-sum expansion for additive-envelope associativity

The outer summands in the two associated matrix composites expand to inner
sums by finite-sum linearity of trace-correspondence composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A left-associated outer summand expands over the second intermediate index. -/
theorem TraceAnalyticAdditiveCategory.assocLeftOuterSummand_eq_innerEntrySum
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length)
    (thirdIndex : Fin third.length) :
    TraceAnalyticAdditiveCategory.assocLeftOuterSummand
      left
      middle
      right
      sourceIndex
      targetIndex
      thirdIndex =
      TraceAnalyticAdditiveCategory.assocLeftInnerEntrySum
        left
        middle
        right
        sourceIndex
        targetIndex
        thirdIndex :=
  TraceCorQHom.sum_comp
    Finset.univ
    (fun secondIndex =>
      TraceCorQHom.comp
        (left.entry sourceIndex secondIndex)
        (middle.entry secondIndex thirdIndex))
    (right.entry thirdIndex targetIndex)

/-- A right-associated outer summand expands over the third intermediate index. -/
theorem TraceAnalyticAdditiveCategory.assocRightOuterSummand_eq_innerEntrySum
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length)
    (secondIndex : Fin second.length) :
    TraceAnalyticAdditiveCategory.assocRightOuterSummand
      left
      middle
      right
      sourceIndex
      targetIndex
      secondIndex =
      TraceAnalyticAdditiveCategory.assocRightInnerEntrySum
        left
        middle
        right
        sourceIndex
        targetIndex
        secondIndex :=
  TraceCorQHom.comp_sum
    (left.entry sourceIndex secondIndex)
    Finset.univ
    (fun thirdIndex =>
      TraceCorQHom.comp
        (middle.entry secondIndex thirdIndex)
        (right.entry thirdIndex targetIndex))

end AnalyticMotives
end LFunctions
end Boundary
