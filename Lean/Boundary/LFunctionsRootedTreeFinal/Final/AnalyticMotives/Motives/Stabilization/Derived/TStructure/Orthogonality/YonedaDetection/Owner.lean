import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Owner

/-!
# Yoneda detection for t-structure orthogonality

This file records the detection step used by the eventual `zero'` field of
the analytic derived t-structure: after the truncation exactness calculus
proves that a morphism has zero image under preadditive Yoneda, faithfulness
of preadditive Yoneda turns that detected zero into an actual zero morphism in
the derived analytic motive category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDerivedMotiveCategory

/-- Preadditive Yoneda detects zero morphisms in the derived analytic motive
category. -/
theorem morphism_eq_zero_of_preadditiveYoneda_map_eq_zero
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (yonedaZero :
      (preadditiveYoneda.map morphism :
        preadditiveYoneda.obj source ⟶
          preadditiveYoneda.obj target) =
        0) :
    morphism = 0 :=
  ((preadditiveYoneda :
    TraceAnalyticDerivedMotiveCategory ⥤
      (TraceAnalyticDerivedMotiveCategoryᵒᵖ ⥤ AddCommGrp))
    .map_injective yonedaZero)

/-- Preadditive Yoneda detects equality of morphisms in the derived analytic
motive category. -/
theorem morphism_eq_of_preadditiveYoneda_map_eq
    {source target : TraceAnalyticDerivedMotiveCategory}
    (left right : source ⟶ target)
    (yonedaEquality :
      (preadditiveYoneda.map left :
        preadditiveYoneda.obj source ⟶
          preadditiveYoneda.obj target) =
        preadditiveYoneda.map right) :
    left = right :=
  ((preadditiveYoneda :
    TraceAnalyticDerivedMotiveCategory ⥤
      (TraceAnalyticDerivedMotiveCategoryᵒᵖ ⥤ AddCommGrp))
    .map_injective yonedaEquality)

/-- The contravariant t-structure orthogonality target can be checked after
preadditive Yoneda. -/
theorem tStructure_zero_field_of_preadditiveYoneda_map_eq_zero
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (_sourceMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source)
    (_targetMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target)
    (yonedaZero :
      (preadditiveYoneda.map morphism :
        preadditiveYoneda.obj source ⟶
          preadditiveYoneda.obj target) =
        0) :
    morphism = 0 :=
  TraceAnalyticDerivedMotiveCategory
    .morphism_eq_zero_of_preadditiveYoneda_map_eq_zero
      morphism
      yonedaZero

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
