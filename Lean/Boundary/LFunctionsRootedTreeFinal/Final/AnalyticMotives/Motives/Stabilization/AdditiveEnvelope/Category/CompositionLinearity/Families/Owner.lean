import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.CompositionLinearity.Comparisons.Owner

/-!
# Indexed summand families for composition linearity

This file names the middle-indexed families whose finite sums are the entries
of the composition-linearity comparison matrices.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The summand family for composing a zero left matrix with a right matrix. -/
def TraceAnalyticAdditiveCategory.zeroLeftCompositionSummand
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  TraceCorQHom.comp
    ((TraceAnalyticAdditiveCategory.zeroHom source middle).entry
      sourceIndex
      middleIndex)
    (right.entry middleIndex targetIndex)

/-- The summand family for composing a left matrix with a zero right matrix. -/
def TraceAnalyticAdditiveCategory.zeroRightCompositionSummand
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  TraceCorQHom.comp
    (left.entry sourceIndex middleIndex)
    ((TraceAnalyticAdditiveCategory.zeroHom middle target).entry
      middleIndex
      targetIndex)

/-- The zero-valued summand family for a fixed source and target entry. -/
def TraceAnalyticAdditiveCategory.zeroCompositionTargetSummand
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (_middleIndex : Fin middle.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  (TraceAnalyticAdditiveCategory.zeroHom source target).entry
    sourceIndex
    targetIndex

/-- The summand family for the source side of left-additivity of composition. -/
def TraceAnalyticAdditiveCategory.addLeftCompositionSummand
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  TraceCorQHom.comp
    ((TraceAnalyticAdditiveCategory.addHom left right).entry
      sourceIndex
      middleIndex)
    (tail.entry middleIndex targetIndex)

/-- The summand family for the target side of left-additivity of composition. -/
def TraceAnalyticAdditiveCategory.leftCompositionAddExpansionSummand
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  TraceCorQHom.add
    (TraceCorQHom.comp
      (left.entry sourceIndex middleIndex)
      (tail.entry middleIndex targetIndex))
    (TraceCorQHom.comp
      (right.entry sourceIndex middleIndex)
      (tail.entry middleIndex targetIndex))

/-- The summand family for the source side of right-additivity of composition. -/
def TraceAnalyticAdditiveCategory.addRightCompositionSummand
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  TraceCorQHom.comp
    (head.entry sourceIndex middleIndex)
    ((TraceAnalyticAdditiveCategory.addHom left right).entry
      middleIndex
      targetIndex)

/-- The summand family for the target side of right-additivity of composition. -/
def TraceAnalyticAdditiveCategory.rightCompositionAddExpansionSummand
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  TraceCorQHom.add
    (TraceCorQHom.comp
      (head.entry sourceIndex middleIndex)
      (left.entry middleIndex targetIndex))
    (TraceCorQHom.comp
      (head.entry sourceIndex middleIndex)
      (right.entry middleIndex targetIndex))

/-- The summand family for the source side of left scalar-linearity of composition. -/
def TraceAnalyticAdditiveCategory.smulLeftCompositionSummand
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  TraceCorQHom.comp
    ((TraceAnalyticAdditiveCategory.smulHom coefficient left).entry
      sourceIndex
      middleIndex)
    (right.entry middleIndex targetIndex)

/-- The summand family for the target side of scalar-linearity of composition. -/
def TraceAnalyticAdditiveCategory.compositionSmulExpansionSummand
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  TraceCorQHom.smul
    coefficient
    (TraceCorQHom.comp
      (left.entry sourceIndex middleIndex)
      (right.entry middleIndex targetIndex))

/-- The summand family for the source side of right scalar-linearity of composition. -/
def TraceAnalyticAdditiveCategory.smulRightCompositionSummand
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  TraceCorQHom.comp
    (left.entry sourceIndex middleIndex)
    ((TraceAnalyticAdditiveCategory.smulHom coefficient right).entry
      middleIndex
      targetIndex)

/-- Pointwise comparison for the left-zero composition summand family. -/
theorem TraceAnalyticAdditiveCategory.zeroLeftCompositionSummand_eq_target
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceAnalyticAdditiveCategory.zeroLeftCompositionSummand
      right
      sourceIndex
      targetIndex
      middleIndex =
      TraceAnalyticAdditiveCategory.zeroCompositionTargetSummand
        sourceIndex
        targetIndex
        middleIndex :=
  TraceAnalyticAdditiveCategory.zero_left_comp_summand
    right
    sourceIndex
    middleIndex
    targetIndex

/-- Pointwise comparison for the right-zero composition summand family. -/
theorem TraceAnalyticAdditiveCategory.zeroRightCompositionSummand_eq_target
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceAnalyticAdditiveCategory.zeroRightCompositionSummand
      left
      sourceIndex
      targetIndex
      middleIndex =
      TraceAnalyticAdditiveCategory.zeroCompositionTargetSummand
        sourceIndex
        targetIndex
        middleIndex :=
  TraceAnalyticAdditiveCategory.comp_zero_right_summand
    left
    sourceIndex
    middleIndex
    targetIndex

/-- Pointwise comparison for the left-additivity summand families. -/
theorem TraceAnalyticAdditiveCategory.addLeftCompositionSummand_eq_expansion
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceAnalyticAdditiveCategory.addLeftCompositionSummand
      left
      right
      tail
      sourceIndex
      targetIndex
      middleIndex =
      TraceAnalyticAdditiveCategory.leftCompositionAddExpansionSummand
        left
        right
        tail
        sourceIndex
        targetIndex
        middleIndex :=
  TraceAnalyticAdditiveCategory.add_left_comp_summand
    left
    right
    tail
    sourceIndex
    middleIndex
    targetIndex

/-- Pointwise comparison for the right-additivity summand families. -/
theorem TraceAnalyticAdditiveCategory.addRightCompositionSummand_eq_expansion
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceAnalyticAdditiveCategory.addRightCompositionSummand
      head
      left
      right
      sourceIndex
      targetIndex
      middleIndex =
      TraceAnalyticAdditiveCategory.rightCompositionAddExpansionSummand
        head
        left
        right
        sourceIndex
        targetIndex
        middleIndex :=
  TraceAnalyticAdditiveCategory.comp_add_right_summand
    head
    left
    right
    sourceIndex
    middleIndex
    targetIndex

/-- Pointwise comparison for the left scalar-linearity summand families. -/
theorem TraceAnalyticAdditiveCategory.smulLeftCompositionSummand_eq_expansion
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceAnalyticAdditiveCategory.smulLeftCompositionSummand
      coefficient
      left
      right
      sourceIndex
      targetIndex
      middleIndex =
      TraceAnalyticAdditiveCategory.compositionSmulExpansionSummand
        coefficient
        left
        right
        sourceIndex
        targetIndex
        middleIndex :=
  TraceAnalyticAdditiveCategory.smul_left_comp_summand
    coefficient
    left
    right
    sourceIndex
    middleIndex
    targetIndex

/-- Pointwise comparison for the right scalar-linearity summand families. -/
theorem TraceAnalyticAdditiveCategory.smulRightCompositionSummand_eq_expansion
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin middle.length) :
    TraceAnalyticAdditiveCategory.smulRightCompositionSummand
      coefficient
      left
      right
      sourceIndex
      targetIndex
      middleIndex =
      TraceAnalyticAdditiveCategory.compositionSmulExpansionSummand
        coefficient
        left
        right
        sourceIndex
        targetIndex
        middleIndex :=
  TraceAnalyticAdditiveCategory.comp_smul_right_summand
    coefficient
    left
    right
    sourceIndex
    middleIndex
    targetIndex

end AnalyticMotives
end LFunctions
end Boundary
