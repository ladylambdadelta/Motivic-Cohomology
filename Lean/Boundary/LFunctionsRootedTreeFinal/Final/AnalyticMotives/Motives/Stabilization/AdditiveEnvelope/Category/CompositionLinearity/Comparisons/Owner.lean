import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.CompositionLinearity.Summands.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Entries.Owner

/-!
# Matrix comparison targets for composition linearity

This file names the full matrix homs on both sides of the composition-linearity
identities.  Their entry formulas are the concrete finite sums to be compared
using the summand-level identities.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Left-zero composition matrix. -/
def TraceAnalyticAdditiveCategory.zeroLeftComposition
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveCategory.comp
    (TraceAnalyticAdditiveCategory.zeroHom source middle)
    right

/-- Right-zero composition matrix. -/
def TraceAnalyticAdditiveCategory.zeroRightComposition
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveCategory.comp
    left
    (TraceAnalyticAdditiveCategory.zeroHom middle target)

/-- Left-additivity source matrix for composition. -/
def TraceAnalyticAdditiveCategory.addLeftComposition
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveCategory.comp
    (TraceAnalyticAdditiveCategory.addHom left right)
    tail

/-- Left-additivity target matrix for composition. -/
def TraceAnalyticAdditiveCategory.leftCompositionAddExpansion
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveCategory.addHom
    (TraceAnalyticAdditiveCategory.comp left tail)
    (TraceAnalyticAdditiveCategory.comp right tail)

/-- Right-additivity source matrix for composition. -/
def TraceAnalyticAdditiveCategory.addRightComposition
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveCategory.comp
    head
    (TraceAnalyticAdditiveCategory.addHom left right)

/-- Right-additivity target matrix for composition. -/
def TraceAnalyticAdditiveCategory.rightCompositionAddExpansion
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveCategory.addHom
    (TraceAnalyticAdditiveCategory.comp head left)
    (TraceAnalyticAdditiveCategory.comp head right)

/-- Left-scalar composition source matrix. -/
def TraceAnalyticAdditiveCategory.smulLeftComposition
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveCategory.comp
    (TraceAnalyticAdditiveCategory.smulHom coefficient left)
    right

/-- Left-scalar composition target matrix. -/
def TraceAnalyticAdditiveCategory.leftCompositionSmulExpansion
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveCategory.smulHom
    coefficient
    (TraceAnalyticAdditiveCategory.comp left right)

/-- Right-scalar composition source matrix. -/
def TraceAnalyticAdditiveCategory.smulRightComposition
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveCategory.comp
    left
    (TraceAnalyticAdditiveCategory.smulHom coefficient right)

/-- Right-scalar composition target matrix. -/
def TraceAnalyticAdditiveCategory.rightCompositionSmulExpansion
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveCategory.smulHom
    coefficient
    (TraceAnalyticAdditiveCategory.comp left right)

/-- Entry formula for the left-zero composition matrix. -/
theorem TraceAnalyticAdditiveCategory.zeroLeftComposition_entry
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.zeroLeftComposition right).entry
      sourceIndex
      targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.zeroHom source middle).entry
              sourceIndex
              middleIndex)
            (right.entry middleIndex targetIndex)) :=
  rfl

/-- Entry formula for the right-zero composition matrix. -/
theorem TraceAnalyticAdditiveCategory.zeroRightComposition_entry
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.zeroRightComposition left).entry
      sourceIndex
      targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            (left.entry sourceIndex middleIndex)
            ((TraceAnalyticAdditiveCategory.zeroHom middle target).entry
              middleIndex
              targetIndex)) :=
  rfl

/-- Entry formula for the left-additivity source matrix. -/
theorem TraceAnalyticAdditiveCategory.addLeftComposition_entry
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.addLeftComposition
      left
      right
      tail).entry sourceIndex targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.addHom left right).entry
              sourceIndex
              middleIndex)
            (tail.entry middleIndex targetIndex)) :=
  rfl

/-- Entry formula for the left-additivity target matrix. -/
theorem TraceAnalyticAdditiveCategory.leftCompositionAddExpansion_entry
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.leftCompositionAddExpansion
      left
      right
      tail).entry sourceIndex targetIndex =
      TraceCorQHom.add
        ((TraceAnalyticAdditiveCategory.comp left tail).entry
          sourceIndex
          targetIndex)
        ((TraceAnalyticAdditiveCategory.comp right tail).entry
          sourceIndex
          targetIndex) :=
  rfl

/-- Entry formula for the right-additivity source matrix. -/
theorem TraceAnalyticAdditiveCategory.addRightComposition_entry
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.addRightComposition
      head
      left
      right).entry sourceIndex targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            (head.entry sourceIndex middleIndex)
            ((TraceAnalyticAdditiveCategory.addHom left right).entry
              middleIndex
              targetIndex)) :=
  rfl

/-- Entry formula for the right-additivity target matrix. -/
theorem TraceAnalyticAdditiveCategory.rightCompositionAddExpansion_entry
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.rightCompositionAddExpansion
      head
      left
      right).entry sourceIndex targetIndex =
      TraceCorQHom.add
        ((TraceAnalyticAdditiveCategory.comp head left).entry
          sourceIndex
          targetIndex)
        ((TraceAnalyticAdditiveCategory.comp head right).entry
          sourceIndex
          targetIndex) :=
  rfl

/-- Entry formula for the left-scalar composition source matrix. -/
theorem TraceAnalyticAdditiveCategory.smulLeftComposition_entry
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.smulLeftComposition
      coefficient
      left
      right).entry sourceIndex targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.smulHom coefficient left).entry
              sourceIndex
              middleIndex)
            (right.entry middleIndex targetIndex)) :=
  rfl

/-- Entry formula for the left-scalar composition target matrix. -/
theorem TraceAnalyticAdditiveCategory.leftCompositionSmulExpansion_entry
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.leftCompositionSmulExpansion
      coefficient
      left
      right).entry sourceIndex targetIndex =
      TraceCorQHom.smul
        coefficient
        ((TraceAnalyticAdditiveCategory.comp left right).entry
          sourceIndex
          targetIndex) :=
  rfl

/-- Entry formula for the right-scalar composition source matrix. -/
theorem TraceAnalyticAdditiveCategory.smulRightComposition_entry
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.smulRightComposition
      coefficient
      left
      right).entry sourceIndex targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            (left.entry sourceIndex middleIndex)
            ((TraceAnalyticAdditiveCategory.smulHom coefficient right).entry
              middleIndex
              targetIndex)) :=
  rfl

/-- Entry formula for the right-scalar composition target matrix. -/
theorem TraceAnalyticAdditiveCategory.rightCompositionSmulExpansion_entry
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.rightCompositionSmulExpansion
      coefficient
      left
      right).entry sourceIndex targetIndex =
      TraceCorQHom.smul
        coefficient
        ((TraceAnalyticAdditiveCategory.comp left right).entry
          sourceIndex
          targetIndex) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
