import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.CompositionLinearity.Families.Owner

/-!
# Finite sums for composition-linearity entries

This file names the finite sums of the indexed summand families used in the
matrix-entry proofs of composition linearity.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The finite sum for a left-zero composition entry. -/
def TraceAnalyticAdditiveCategory.zeroLeftCompositionEntrySum
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.zeroLeftCompositionSummand
      right
      sourceIndex
      targetIndex)

/-- The finite sum for a right-zero composition entry. -/
def TraceAnalyticAdditiveCategory.zeroRightCompositionEntrySum
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.zeroRightCompositionSummand
      left
      sourceIndex
      targetIndex)

/-- The finite sum for the zero target entry family. -/
def TraceAnalyticAdditiveCategory.zeroCompositionTargetEntrySum
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.zeroCompositionTargetSummand
      (middle := middle)
      sourceIndex
      targetIndex)

/-- The finite sum for the source side of left-additivity of composition. -/
def TraceAnalyticAdditiveCategory.addLeftCompositionEntrySum
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.addLeftCompositionSummand
      left
      right
      tail
      sourceIndex
      targetIndex)

/-- The finite sum for the target side of left-additivity of composition. -/
def TraceAnalyticAdditiveCategory.leftCompositionAddExpansionEntrySum
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.leftCompositionAddExpansionSummand
      left
      right
      tail
      sourceIndex
      targetIndex)

/-- The finite sum for the source side of right-additivity of composition. -/
def TraceAnalyticAdditiveCategory.addRightCompositionEntrySum
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.addRightCompositionSummand
      head
      left
      right
      sourceIndex
      targetIndex)

/-- The finite sum for the target side of right-additivity of composition. -/
def TraceAnalyticAdditiveCategory.rightCompositionAddExpansionEntrySum
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.rightCompositionAddExpansionSummand
      head
      left
      right
      sourceIndex
      targetIndex)

/-- The finite sum for the source side of left scalar-linearity of composition. -/
def TraceAnalyticAdditiveCategory.smulLeftCompositionEntrySum
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.smulLeftCompositionSummand
      coefficient
      left
      right
      sourceIndex
      targetIndex)

/-- The finite sum for the target side of scalar-linearity of composition. -/
def TraceAnalyticAdditiveCategory.compositionSmulExpansionEntrySum
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.compositionSmulExpansionSummand
      coefficient
      left
      right
      sourceIndex
      targetIndex)

/-- The finite sum for the source side of right scalar-linearity of composition. -/
def TraceAnalyticAdditiveCategory.smulRightCompositionEntrySum
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.smulRightCompositionSummand
      coefficient
      left
      right
      sourceIndex
      targetIndex)

/-- The left-zero comparison entry is its named finite summand-family sum. -/
theorem TraceAnalyticAdditiveCategory.zeroLeftComposition_entry_eq_sum
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.zeroLeftComposition right).entry
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.zeroLeftCompositionEntrySum
        right
        sourceIndex
        targetIndex :=
  rfl

/-- The right-zero comparison entry is its named finite summand-family sum. -/
theorem TraceAnalyticAdditiveCategory.zeroRightComposition_entry_eq_sum
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.zeroRightComposition left).entry
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.zeroRightCompositionEntrySum
        left
        sourceIndex
        targetIndex :=
  rfl

/-- The left-additivity source entry is its named finite summand-family sum. -/
theorem TraceAnalyticAdditiveCategory.addLeftComposition_entry_eq_sum
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.addLeftComposition
      left
      right
      tail).entry sourceIndex targetIndex =
      TraceAnalyticAdditiveCategory.addLeftCompositionEntrySum
        left
        right
        tail
        sourceIndex
        targetIndex :=
  rfl

/-- The right-additivity source entry is its named finite summand-family sum. -/
theorem TraceAnalyticAdditiveCategory.addRightComposition_entry_eq_sum
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.addRightComposition
      head
      left
      right).entry sourceIndex targetIndex =
      TraceAnalyticAdditiveCategory.addRightCompositionEntrySum
        head
        left
        right
        sourceIndex
        targetIndex :=
  rfl

/-- The left scalar-linearity source entry is its named finite summand-family sum. -/
theorem TraceAnalyticAdditiveCategory.smulLeftComposition_entry_eq_sum
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
      TraceAnalyticAdditiveCategory.smulLeftCompositionEntrySum
        coefficient
        left
        right
        sourceIndex
        targetIndex :=
  rfl

/-- The right scalar-linearity source entry is its named finite summand-family sum. -/
theorem TraceAnalyticAdditiveCategory.smulRightComposition_entry_eq_sum
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
      TraceAnalyticAdditiveCategory.smulRightCompositionEntrySum
        coefficient
        left
        right
        sourceIndex
        targetIndex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
