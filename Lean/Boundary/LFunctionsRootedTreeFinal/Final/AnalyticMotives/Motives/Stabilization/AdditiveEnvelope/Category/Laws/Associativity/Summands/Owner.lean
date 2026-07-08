import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Associativity.FiniteSums.Owner

/-!
# Pointwise associativity for additive-envelope summands

This file applies associativity of the underlying trace-correspondence category
to each fixed pair of intermediate indices in the additive-envelope matrix
composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Fixed intermediate indices associate by the trace-correspondence law. -/
theorem TraceAnalyticAdditiveCategory.assocInnerSummand_eq
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length)
    (secondIndex : Fin second.length)
    (thirdIndex : Fin third.length) :
    TraceCorQHom.comp
      (TraceCorQHom.comp
        (left.entry sourceIndex secondIndex)
        (middle.entry secondIndex thirdIndex))
      (right.entry thirdIndex targetIndex) =
      TraceCorQHom.comp
        (left.entry sourceIndex secondIndex)
        (TraceCorQHom.comp
          (middle.entry secondIndex thirdIndex)
          (right.entry thirdIndex targetIndex)) :=
  TraceCorQHom.comp_assoc
    (left.entry sourceIndex secondIndex)
    (middle.entry secondIndex thirdIndex)
    (right.entry thirdIndex targetIndex)

/-- The named left inner summand equals the associated right inner summand. -/
theorem TraceAnalyticAdditiveCategory.assocLeftInnerSummand_eq_rightInnerSummand
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length)
    (secondIndex : Fin second.length)
    (thirdIndex : Fin third.length) :
    TraceAnalyticAdditiveCategory.assocLeftInnerSummand
      left
      middle
      right
      sourceIndex
      targetIndex
      thirdIndex
      secondIndex =
      TraceAnalyticAdditiveCategory.assocRightInnerSummand
        left
        middle
        right
        sourceIndex
        targetIndex
        secondIndex
        thirdIndex :=
  TraceAnalyticAdditiveCategory.assocInnerSummand_eq
    left
    middle
    right
    sourceIndex
    targetIndex
    secondIndex
    thirdIndex

end AnalyticMotives
end LFunctions
end Boundary
