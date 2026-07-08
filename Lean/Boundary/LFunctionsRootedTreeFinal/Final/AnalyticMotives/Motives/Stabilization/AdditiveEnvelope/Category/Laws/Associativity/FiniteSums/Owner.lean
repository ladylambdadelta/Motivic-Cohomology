import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Associativity.Families.Owner

/-!
# Associativity-law finite sums

This file names the finite sums of the associativity-law summand families and
links the comparison-matrix entries to the outer sums.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The outer finite sum for the left-associated composite entry. -/
def TraceAnalyticAdditiveCategory.assocLeftOuterEntrySum
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length) :
    TraceCorQHom
      (first.component sourceIndex)
      (fourth.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.assocLeftOuterSummand
      left
      middle
      right
      sourceIndex
      targetIndex)

/-- The outer finite sum for the right-associated composite entry. -/
def TraceAnalyticAdditiveCategory.assocRightOuterEntrySum
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length) :
    TraceCorQHom
      (first.component sourceIndex)
      (fourth.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.assocRightOuterSummand
      left
      middle
      right
      sourceIndex
      targetIndex)

/-- The inner finite sum for the left-associated composite at a fixed third index. -/
def TraceAnalyticAdditiveCategory.assocLeftInnerEntrySum
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length)
    (thirdIndex : Fin third.length) :
    TraceCorQHom
      (first.component sourceIndex)
      (fourth.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.assocLeftInnerSummand
      left
      middle
      right
      sourceIndex
      targetIndex
      thirdIndex)

/-- The inner finite sum for the right-associated composite at a fixed second index. -/
def TraceAnalyticAdditiveCategory.assocRightInnerEntrySum
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length)
    (secondIndex : Fin second.length) :
    TraceCorQHom
      (first.component sourceIndex)
      (fourth.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.assocRightInnerSummand
      left
      middle
      right
      sourceIndex
      targetIndex
      secondIndex)

/-- The left-associated comparison entry is its named outer finite sum. -/
theorem TraceAnalyticAdditiveCategory.assocLeftComposite_entry_eq_outerSum
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length) :
    (TraceAnalyticAdditiveCategory.assocLeftComposite
      left
      middle
      right).entry sourceIndex targetIndex =
      TraceAnalyticAdditiveCategory.assocLeftOuterEntrySum
        left
        middle
        right
        sourceIndex
        targetIndex :=
  rfl

/-- The right-associated comparison entry is its named outer finite sum. -/
theorem TraceAnalyticAdditiveCategory.assocRightComposite_entry_eq_outerSum
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length) :
    (TraceAnalyticAdditiveCategory.assocRightComposite
      left
      middle
      right).entry sourceIndex targetIndex =
      TraceAnalyticAdditiveCategory.assocRightOuterEntrySum
        left
        middle
        right
        sourceIndex
        targetIndex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
