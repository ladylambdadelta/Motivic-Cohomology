import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.CompositionLinearity.FiniteSums.Distribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Ext.Owner

/-!
# Additive and scalar composition-linearity laws

This file assembles the entrywise finite-sum comparisons into full matrix-hom
equalities for additive and scalar linearity of analytic additive-envelope
composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Matrix composition is additive in the left input. -/
theorem TraceAnalyticAdditiveCategory.add_left_comp
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.addLeftComposition left right tail =
      TraceAnalyticAdditiveCategory.leftCompositionAddExpansion left right tail :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      Eq.trans
        (TraceAnalyticAdditiveCategory.addLeftComposition_entry_eq_sum
          left
          right
          tail
          sourceIndex
          targetIndex)
        (Eq.trans
          (TraceAnalyticAdditiveCategory.addLeftCompositionEntrySum_eq_expansion
            left
            right
            tail
            sourceIndex
            targetIndex)
          (TraceAnalyticAdditiveCategory.leftCompositionAddExpansionEntrySum_eq_entry
            left
            right
            tail
            sourceIndex
            targetIndex)))

/-- Matrix composition is additive in the right input. -/
theorem TraceAnalyticAdditiveCategory.comp_add_right
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.addRightComposition head left right =
      TraceAnalyticAdditiveCategory.rightCompositionAddExpansion head left right :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      Eq.trans
        (TraceAnalyticAdditiveCategory.addRightComposition_entry_eq_sum
          head
          left
          right
          sourceIndex
          targetIndex)
        (Eq.trans
          (TraceAnalyticAdditiveCategory.addRightCompositionEntrySum_eq_expansion
            head
            left
            right
            sourceIndex
            targetIndex)
          (TraceAnalyticAdditiveCategory.rightCompositionAddExpansionEntrySum_eq_entry
            head
            left
            right
            sourceIndex
            targetIndex)))

/-- Scaling the left input scales matrix composition. -/
theorem TraceAnalyticAdditiveCategory.smul_left_comp
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.smulLeftComposition coefficient left right =
      TraceAnalyticAdditiveCategory.leftCompositionSmulExpansion
        coefficient
        left
        right :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      Eq.trans
        (TraceAnalyticAdditiveCategory.smulLeftComposition_entry_eq_sum
          coefficient
          left
          right
          sourceIndex
          targetIndex)
        (Eq.trans
          (TraceAnalyticAdditiveCategory.smulLeftCompositionEntrySum_eq_expansion
            coefficient
            left
            right
            sourceIndex
            targetIndex)
          (TraceAnalyticAdditiveCategory.compositionSmulExpansionEntrySum_eq_leftEntry
            coefficient
            left
            right
            sourceIndex
            targetIndex)))

/-- Scaling the right input scales matrix composition. -/
theorem TraceAnalyticAdditiveCategory.comp_smul_right
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.smulRightComposition coefficient left right =
      TraceAnalyticAdditiveCategory.rightCompositionSmulExpansion
        coefficient
        left
        right :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      Eq.trans
        (TraceAnalyticAdditiveCategory.smulRightComposition_entry_eq_sum
          coefficient
          left
          right
          sourceIndex
          targetIndex)
        (Eq.trans
          (TraceAnalyticAdditiveCategory.smulRightCompositionEntrySum_eq_expansion
            coefficient
            left
            right
            sourceIndex
            targetIndex)
          (TraceAnalyticAdditiveCategory.compositionSmulExpansionEntrySum_eq_rightEntry
            coefficient
            left
            right
            sourceIndex
            targetIndex)))

end AnalyticMotives
end LFunctions
end Boundary
