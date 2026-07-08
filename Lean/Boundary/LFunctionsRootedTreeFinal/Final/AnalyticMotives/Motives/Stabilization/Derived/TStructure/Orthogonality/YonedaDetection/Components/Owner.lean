import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.YonedaDetection.Owner

/-!
# Componentwise Yoneda detection for t-structure orthogonality

This file refines the faithful-Yoneda detection step to the form produced by
short-complex exactness calculations: if every component of the preadditive
Yoneda image of a morphism is zero, then the morphism itself is zero.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDerivedMotiveCategory

/-- A preadditive Yoneda component evaluates a morphism by postcomposition. -/
theorem preadditiveYoneda_map_app_apply_eq_comp
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (hom : (preadditiveYoneda.obj source).obj probe) :
    ((preadditiveYoneda.map morphism).app probe) hom =
      hom ≫ morphism :=
  rfl

/-- A morphism whose preadditive Yoneda image is componentwise zero is zero. -/
theorem morphism_eq_zero_of_preadditiveYoneda_components_eq_zero
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (componentZero :
      ∀ probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ,
        ((preadditiveYoneda.map morphism).app probe :
          (preadditiveYoneda.obj source).obj probe ⟶
            (preadditiveYoneda.obj target).obj probe) =
          0) :
    morphism = 0 :=
  TraceAnalyticDerivedMotiveCategory
    .morphism_eq_zero_of_preadditiveYoneda_map_eq_zero
      morphism
      (NatTrans.ext
        (funext fun probe =>
          componentZero probe))

/-- Elementwise zero of every preadditive Yoneda component detects a zero
morphism. -/
theorem morphism_eq_zero_of_preadditiveYoneda_apply_eq_zero
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (componentApplyZero :
      ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
        ∀ hom :
          (preadditiveYoneda.obj source).obj probe,
          ((preadditiveYoneda.map morphism).app probe) hom = 0) :
    morphism = 0 :=
  TraceAnalyticDerivedMotiveCategory
    .morphism_eq_zero_of_preadditiveYoneda_components_eq_zero
      morphism
      (fun probe =>
        AddMonoidHom.ext
          (componentApplyZero probe))

/-- Vanishing of all postcompositions into a morphism detects that the
morphism is zero. -/
theorem morphism_eq_zero_of_postcomp_eq_zero
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (postcompZero :
      ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
        ∀ hom : probe.unop ⟶ source,
          hom ≫ morphism = 0) :
    morphism = 0 :=
  TraceAnalyticDerivedMotiveCategory
    .morphism_eq_zero_of_preadditiveYoneda_apply_eq_zero
      morphism
      (fun probe hom =>
        Eq.trans
          (TraceAnalyticDerivedMotiveCategory
            .preadditiveYoneda_map_app_apply_eq_comp
              morphism
              probe
              hom)
          (postcompZero probe hom))

/-- The Mathlib `zero'`-field binder shape follows from elementwise zero of
all preadditive Yoneda components. -/
theorem tStructure_zero_field_of_preadditiveYoneda_apply_eq_zero
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (_sourceMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source)
    (_targetMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target)
    (componentApplyZero :
      ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
        ∀ hom :
          (preadditiveYoneda.obj source).obj probe,
          ((preadditiveYoneda.map morphism).app probe) hom = 0) :
    morphism = 0 :=
  TraceAnalyticDerivedMotiveCategory
    .morphism_eq_zero_of_preadditiveYoneda_apply_eq_zero
      morphism
      componentApplyZero

/-- The Mathlib `zero'`-field binder shape follows from vanishing of all
postcompositions into the morphism. -/
theorem tStructure_zero_field_of_postcomp_eq_zero
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (_sourceMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source)
    (_targetMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target)
    (postcompZero :
      ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
        ∀ hom : probe.unop ⟶ source,
          hom ≫ morphism = 0) :
    morphism = 0 :=
  TraceAnalyticDerivedMotiveCategory
    .morphism_eq_zero_of_postcomp_eq_zero
      morphism
      postcompZero

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
