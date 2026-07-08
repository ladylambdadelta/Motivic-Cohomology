import Mathlib.Algebra.Module.BigOperators
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.CompositionLinearity.FiniteSums.Congruence.Owner

/-!
# Finite-sum distribution for composition-linearity entries

This file identifies the expanded finite sums with the target-side additive
and scalar entries of the composition-linearity comparison matrices.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-additivity expansion sum is the target matrix entry. -/
theorem TraceAnalyticAdditiveCategory.leftCompositionAddExpansionEntrySum_eq_entry
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.leftCompositionAddExpansionEntrySum
      left
      right
      tail
      sourceIndex
      targetIndex =
      (TraceAnalyticAdditiveCategory.leftCompositionAddExpansion
        left
        right
        tail).entry sourceIndex targetIndex :=
  Finset.sum_add_distrib

/-- The right-additivity expansion sum is the target matrix entry. -/
theorem TraceAnalyticAdditiveCategory.rightCompositionAddExpansionEntrySum_eq_entry
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.rightCompositionAddExpansionEntrySum
      head
      left
      right
      sourceIndex
      targetIndex =
      (TraceAnalyticAdditiveCategory.rightCompositionAddExpansion
        head
        left
        right).entry sourceIndex targetIndex :=
  Finset.sum_add_distrib

/-- The scalar expansion sum is the left-scalar target matrix entry. -/
theorem TraceAnalyticAdditiveCategory.compositionSmulExpansionEntrySum_eq_leftEntry
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.compositionSmulExpansionEntrySum
      coefficient
      left
      right
      sourceIndex
      targetIndex =
      (TraceAnalyticAdditiveCategory.leftCompositionSmulExpansion
        coefficient
        left
        right).entry sourceIndex targetIndex :=
  Eq.symm
    Finset.smul_sum

/-- The scalar expansion sum is the right-scalar target matrix entry. -/
theorem TraceAnalyticAdditiveCategory.compositionSmulExpansionEntrySum_eq_rightEntry
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.compositionSmulExpansionEntrySum
      coefficient
      left
      right
      sourceIndex
      targetIndex =
      (TraceAnalyticAdditiveCategory.rightCompositionSmulExpansion
        coefficient
        left
        right).entry sourceIndex targetIndex :=
  Eq.symm
    Finset.smul_sum

end AnalyticMotives
end LFunctions
end Boundary
