import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Additive.Structures.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.CompositionLinearity.Public.Owner

/-!
# Standard-notation linearity for additive-envelope composition

This file translates the named-operation composition-linearity laws into the
standard operations used by Mathlib's `Preadditive` and `Linear` structures.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Standard composition is additive in the left input. -/
theorem TraceAnalyticAdditiveCategory.std_add_comp
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.comp
      (left + right)
      tail =
      TraceAnalyticAdditiveCategory.comp left tail +
        TraceAnalyticAdditiveCategory.comp right tail :=
  Eq.trans
    (congrArg
      (fun head =>
        TraceAnalyticAdditiveCategory.comp head tail)
      (Eq.symm
        (TraceAnalyticAdditiveCategory.addHom_eq_add left right)))
    (Eq.trans
      (TraceAnalyticAdditiveCategory.comp_addHom_left left right tail)
      (TraceAnalyticAdditiveCategory.addHom_eq_add
        (TraceAnalyticAdditiveCategory.comp left tail)
        (TraceAnalyticAdditiveCategory.comp right tail)))

/-- Standard composition is additive in the right input. -/
theorem TraceAnalyticAdditiveCategory.std_comp_add
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.comp
      head
      (left + right) =
      TraceAnalyticAdditiveCategory.comp head left +
        TraceAnalyticAdditiveCategory.comp head right :=
  Eq.trans
    (congrArg
      (fun tail =>
        TraceAnalyticAdditiveCategory.comp head tail)
      (Eq.symm
        (TraceAnalyticAdditiveCategory.addHom_eq_add left right)))
    (Eq.trans
      (TraceAnalyticAdditiveCategory.comp_addHom_right head left right)
      (TraceAnalyticAdditiveCategory.addHom_eq_add
        (TraceAnalyticAdditiveCategory.comp head left)
        (TraceAnalyticAdditiveCategory.comp head right)))

/-- Standard scalar multiplication on the left input scales composition. -/
theorem TraceAnalyticAdditiveCategory.std_smul_comp
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.comp
      (coefficient • left)
      right =
      coefficient • TraceAnalyticAdditiveCategory.comp left right :=
  Eq.trans
    (congrArg
      (fun head =>
        TraceAnalyticAdditiveCategory.comp head right)
      (Eq.symm
        (TraceAnalyticAdditiveCategory.smulHom_eq_smul
          coefficient
          left)))
    (Eq.trans
      (TraceAnalyticAdditiveCategory.comp_smulHom_left
        coefficient
        left
        right)
      (TraceAnalyticAdditiveCategory.smulHom_eq_smul
        coefficient
        (TraceAnalyticAdditiveCategory.comp left right)))

/-- Standard scalar multiplication on the right input scales composition. -/
theorem TraceAnalyticAdditiveCategory.std_comp_smul
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.comp
      left
      (coefficient • right) =
      coefficient • TraceAnalyticAdditiveCategory.comp left right :=
  Eq.trans
    (congrArg
      (fun tail =>
        TraceAnalyticAdditiveCategory.comp left tail)
      (Eq.symm
        (TraceAnalyticAdditiveCategory.smulHom_eq_smul
          coefficient
          right)))
    (Eq.trans
      (TraceAnalyticAdditiveCategory.comp_smulHom_right
        coefficient
        left
        right)
      (TraceAnalyticAdditiveCategory.smulHom_eq_smul
        coefficient
        (TraceAnalyticAdditiveCategory.comp left right)))

end AnalyticMotives
end LFunctions
end Boundary
