import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.CompositionLinearity.Owner

/-!
# Public composition-linearity laws

This file exposes the composition-linearity laws directly in terms of the
category-level operations `comp`, `zeroHom`, `addHom`, and `smulHom`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composition absorbs the zero hom on the left. -/
theorem TraceAnalyticAdditiveCategory.comp_zeroHom_left
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.comp
      (TraceAnalyticAdditiveCategory.zeroHom source middle)
      right =
      TraceAnalyticAdditiveCategory.zeroHom source target :=
  TraceAnalyticAdditiveCategory.zero_left_comp right

/-- Composition absorbs the zero hom on the right. -/
theorem TraceAnalyticAdditiveCategory.comp_zeroHom_right
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle) :
    TraceAnalyticAdditiveCategory.comp
      left
      (TraceAnalyticAdditiveCategory.zeroHom middle target) =
      TraceAnalyticAdditiveCategory.zeroHom source target :=
  TraceAnalyticAdditiveCategory.comp_zero_right left

/-- Composition is additive in the left input. -/
theorem TraceAnalyticAdditiveCategory.comp_addHom_left
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.comp
      (TraceAnalyticAdditiveCategory.addHom left right)
      tail =
      TraceAnalyticAdditiveCategory.addHom
        (TraceAnalyticAdditiveCategory.comp left tail)
        (TraceAnalyticAdditiveCategory.comp right tail) :=
  TraceAnalyticAdditiveCategory.add_left_comp left right tail

/-- Composition is additive in the right input. -/
theorem TraceAnalyticAdditiveCategory.comp_addHom_right
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.comp
      head
      (TraceAnalyticAdditiveCategory.addHom left right) =
      TraceAnalyticAdditiveCategory.addHom
        (TraceAnalyticAdditiveCategory.comp head left)
        (TraceAnalyticAdditiveCategory.comp head right) :=
  TraceAnalyticAdditiveCategory.comp_add_right head left right

/-- Scaling the left input scales composition. -/
theorem TraceAnalyticAdditiveCategory.comp_smulHom_left
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.comp
      (TraceAnalyticAdditiveCategory.smulHom coefficient left)
      right =
      TraceAnalyticAdditiveCategory.smulHom
        coefficient
        (TraceAnalyticAdditiveCategory.comp left right) :=
  TraceAnalyticAdditiveCategory.smul_left_comp coefficient left right

/-- Scaling the right input scales composition. -/
theorem TraceAnalyticAdditiveCategory.comp_smulHom_right
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.comp
      left
      (TraceAnalyticAdditiveCategory.smulHom coefficient right) =
      TraceAnalyticAdditiveCategory.smulHom
        coefficient
        (TraceAnalyticAdditiveCategory.comp left right) :=
  TraceAnalyticAdditiveCategory.comp_smul_right coefficient left right

end AnalyticMotives
end LFunctions
end Boundary
