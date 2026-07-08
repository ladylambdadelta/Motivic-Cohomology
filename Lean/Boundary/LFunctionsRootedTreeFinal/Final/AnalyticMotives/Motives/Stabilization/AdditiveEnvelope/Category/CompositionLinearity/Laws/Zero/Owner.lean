import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.CompositionLinearity.FiniteSums.Congruence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Ext.Owner

/-!
# Zero composition-linearity laws

This file assembles the zero-composition summand comparisons into full
matrix-hom zero absorption laws for analytic additive-envelope composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero-target summand-family sum is the zero matrix entry. -/
theorem TraceAnalyticAdditiveCategory.zeroCompositionTargetEntrySum_eq_entry
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.zeroCompositionTargetEntrySum
      (middle := middle)
      sourceIndex
      targetIndex =
      (TraceAnalyticAdditiveCategory.zeroHom source target).entry
        sourceIndex
        targetIndex :=
  Finset.sum_const_zero

/-- Matrix composition absorbs the zero hom on the left. -/
theorem TraceAnalyticAdditiveCategory.zero_left_comp
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.zeroLeftComposition right =
      TraceAnalyticAdditiveCategory.zeroHom source target :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      Eq.trans
        (TraceAnalyticAdditiveCategory.zeroLeftComposition_entry_eq_sum
          right
          sourceIndex
          targetIndex)
        (Eq.trans
          (TraceAnalyticAdditiveCategory.zeroLeftCompositionEntrySum_eq_target
            right
            sourceIndex
            targetIndex)
          (TraceAnalyticAdditiveCategory.zeroCompositionTargetEntrySum_eq_entry
            (middle := middle)
            sourceIndex
            targetIndex)))

/-- Matrix composition absorbs the zero hom on the right. -/
theorem TraceAnalyticAdditiveCategory.comp_zero_right
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle) :
    TraceAnalyticAdditiveCategory.zeroRightComposition left =
      TraceAnalyticAdditiveCategory.zeroHom source target :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      Eq.trans
        (TraceAnalyticAdditiveCategory.zeroRightComposition_entry_eq_sum
          left
          sourceIndex
          targetIndex)
        (Eq.trans
          (TraceAnalyticAdditiveCategory.zeroRightCompositionEntrySum_eq_target
            left
            sourceIndex
            targetIndex)
          (TraceAnalyticAdditiveCategory.zeroCompositionTargetEntrySum_eq_entry
            (middle := middle)
            sourceIndex
            targetIndex)))

end AnalyticMotives
end LFunctions
end Boundary
