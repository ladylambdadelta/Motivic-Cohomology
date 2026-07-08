import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Comparisons.Owner

/-!
# Associativity-law summand families

This file names the outer and inner summand families that occur when expanding
the two associated matrix composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The outer summand family for the left-associated composite. -/
def TraceAnalyticAdditiveCategory.assocLeftOuterSummand
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
  TraceCorQHom.comp
    ((TraceAnalyticAdditiveCategory.comp left middle).entry
      sourceIndex
      thirdIndex)
    (right.entry thirdIndex targetIndex)

/-- The outer summand family for the right-associated composite. -/
def TraceAnalyticAdditiveCategory.assocRightOuterSummand
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
  TraceCorQHom.comp
    (left.entry sourceIndex secondIndex)
    ((TraceAnalyticAdditiveCategory.comp middle right).entry
      secondIndex
      targetIndex)

/-- The inner summand family for the left-associated composite at a fixed third index. -/
def TraceAnalyticAdditiveCategory.assocLeftInnerSummand
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length)
    (thirdIndex : Fin third.length)
    (secondIndex : Fin second.length) :
    TraceCorQHom
      (first.component sourceIndex)
      (fourth.component targetIndex) :=
  TraceCorQHom.comp
    (TraceCorQHom.comp
      (left.entry sourceIndex secondIndex)
      (middle.entry secondIndex thirdIndex))
    (right.entry thirdIndex targetIndex)

/-- The inner summand family for the right-associated composite at a fixed second index. -/
def TraceAnalyticAdditiveCategory.assocRightInnerSummand
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length)
    (secondIndex : Fin second.length)
    (thirdIndex : Fin third.length) :
    TraceCorQHom
      (first.component sourceIndex)
      (fourth.component targetIndex) :=
  TraceCorQHom.comp
    (left.entry sourceIndex secondIndex)
    (TraceCorQHom.comp
      (middle.entry secondIndex thirdIndex)
      (right.entry thirdIndex targetIndex))

/-- The left inner summand is the raw nested composite. -/
theorem TraceAnalyticAdditiveCategory.assocLeftInnerSummand_eq_raw
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length)
    (thirdIndex : Fin third.length)
    (secondIndex : Fin second.length) :
    TraceAnalyticAdditiveCategory.assocLeftInnerSummand
      left
      middle
      right
      sourceIndex
      targetIndex
      thirdIndex
      secondIndex =
      TraceCorQHom.comp
        (TraceCorQHom.comp
          (left.entry sourceIndex secondIndex)
          (middle.entry secondIndex thirdIndex))
        (right.entry thirdIndex targetIndex) :=
  rfl

/-- The right inner summand is the raw nested composite. -/
theorem TraceAnalyticAdditiveCategory.assocRightInnerSummand_eq_raw
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length)
    (secondIndex : Fin second.length)
    (thirdIndex : Fin third.length) :
    TraceAnalyticAdditiveCategory.assocRightInnerSummand
      left
      middle
      right
      sourceIndex
      targetIndex
      secondIndex
      thirdIndex =
      TraceCorQHom.comp
        (left.entry sourceIndex secondIndex)
        (TraceCorQHom.comp
          (middle.entry secondIndex thirdIndex)
          (right.entry thirdIndex targetIndex)) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
