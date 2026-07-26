import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Postcomposition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.YonedaDetection.Components.Owner

/-!
# Global homological orthogonality

This file owns the adjacent bounded-derived orthogonality theorem for the
analytic homological predicates.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Homological bounds force elementwise vanishing after preadditive Yoneda.
Faithful Yoneda detection then gives the categorical zero conclusion. -/
theorem globalPreadditiveYonedaApplyZero_of_homologicalBounds :
    ∀ {source target : TraceAnalyticDerivedMotiveCategory},
      ∀ (morphism : source ⟶ target),
        TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
          TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
            ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
              ∀ hom :
                (preadditiveYoneda.obj source).obj probe,
                ((preadditiveYoneda.map morphism).app probe) hom = 0 :=
  fun morphism sourceMembership targetMembership probe hom =>
    Eq.trans
      (TraceAnalyticDerivedMotiveCategory
        .preadditiveYoneda_map_app_apply_eq_comp
          morphism
          probe
          hom)
      (TraceAnalyticDerivedMotiveCategory
        .homologicalBounds_postcompVanishing
          morphism
          sourceMembership
          targetMembership
          probe
          hom)

/-- A morphism from the homological `≤ 0` aisle to the homological `≥ 1`
coaisle is zero. -/
theorem globalZeroField_of_homologicalBounds :
    ∀ {source target : TraceAnalyticDerivedMotiveCategory},
      ∀ (morphism : source ⟶ target),
        TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
          TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
            morphism = 0 :=
  fun morphism sourceMembership targetMembership =>
    TraceAnalyticDerivedMotiveCategory
      .tStructure_zero_field_of_preadditiveYoneda_apply_eq_zero
        morphism
        sourceMembership
        targetMembership
        (TraceAnalyticDerivedMotiveCategory
          .globalPreadditiveYonedaApplyZero_of_homologicalBounds
            morphism
            sourceMembership
            targetMembership)

/-- Bounded-derived orthogonality gives vanishing after postcomposition with
every probe map. -/
theorem globalPostcompVanishing_of_homologicalBounds :
    ∀ {source target : TraceAnalyticDerivedMotiveCategory},
      ∀ (morphism : source ⟶ target),
        TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
          TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
            ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
              ∀ hom : probe.unop ⟶ source,
                hom ≫ morphism = 0 :=
  TraceAnalyticDerivedMotiveCategory.homologicalBounds_postcompVanishing

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
