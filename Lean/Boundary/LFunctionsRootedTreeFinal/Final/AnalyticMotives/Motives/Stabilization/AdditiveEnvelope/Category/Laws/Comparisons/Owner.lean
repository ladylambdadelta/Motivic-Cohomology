import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Entries.Owner

/-!
# Category-law comparison matrices

This file names the concrete matrix homs appearing in the identity and
associativity laws for the analytic additive-envelope category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Left-identity composite for a matrix hom. -/
def TraceAnalyticAdditiveCategory.leftIdentityComposite
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveCategory.comp
    (TraceAnalyticAdditiveCategory.id source)
    hom

/-- Right-identity composite for a matrix hom. -/
def TraceAnalyticAdditiveCategory.rightIdentityComposite
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveCategory.comp
    hom
    (TraceAnalyticAdditiveCategory.id target)

/-- Left-associated triple composite. -/
def TraceAnalyticAdditiveCategory.assocLeftComposite
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth) :
    TraceAnalyticAdditiveCategoryHom first fourth :=
  TraceAnalyticAdditiveCategory.comp
    (TraceAnalyticAdditiveCategory.comp left middle)
    right

/-- Right-associated triple composite. -/
def TraceAnalyticAdditiveCategory.assocRightComposite
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth) :
    TraceAnalyticAdditiveCategoryHom first fourth :=
  TraceAnalyticAdditiveCategory.comp
    left
    (TraceAnalyticAdditiveCategory.comp middle right)

/-- Entry formula for the left-identity composite. -/
theorem TraceAnalyticAdditiveCategory.leftIdentityComposite_entry
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.leftIdentityComposite hom).entry
      sourceIndex
      targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.id source).entry
              sourceIndex
              middleIndex)
            (hom.entry middleIndex targetIndex)) :=
  rfl

/-- Entry formula for the right-identity composite. -/
theorem TraceAnalyticAdditiveCategory.rightIdentityComposite_entry
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.rightIdentityComposite hom).entry
      sourceIndex
      targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            (hom.entry sourceIndex middleIndex)
            ((TraceAnalyticAdditiveCategory.id target).entry
              middleIndex
              targetIndex)) :=
  rfl

/-- Entry formula for the left-associated triple composite. -/
theorem TraceAnalyticAdditiveCategory.assocLeftComposite_entry
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
      Finset.univ.sum
        (fun thirdIndex =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.comp left middle).entry
              sourceIndex
              thirdIndex)
            (right.entry thirdIndex targetIndex)) :=
  rfl

/-- Entry formula for the right-associated triple composite. -/
theorem TraceAnalyticAdditiveCategory.assocRightComposite_entry
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
      Finset.univ.sum
        (fun secondIndex =>
          TraceCorQHom.comp
            (left.entry sourceIndex secondIndex)
            ((TraceAnalyticAdditiveCategory.comp middle right).entry
              secondIndex
              targetIndex)) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
