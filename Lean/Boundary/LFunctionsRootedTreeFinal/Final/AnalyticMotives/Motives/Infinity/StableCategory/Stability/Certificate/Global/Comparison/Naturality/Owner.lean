import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Cofiber.Comparison.Projections.Naturality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Fiber.Comparison.Projections.Naturality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Comparison.Owner

/-!
# Global naturality certificate for comparison short complexes

This file bundles the naturality laws for cofiber and fiber short-complex
comparison maps attached to a commutative square in the concrete analytic
stable category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The global comparison package is natural with respect to the two
short-complex structure maps, for both chosen cofiber and chosen fiber short
complexes. -/
theorem traceAnalyticStableInfinityCategory_global_comparison_naturality :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      sourceMap ≫
          (ShortComplex.π₁Toπ₂ :
            (ShortComplex.π₁ :
              ShortComplex StableInfinityOwner.PresentedCategory ⥤
                StableInfinityOwner.PresentedCategory) ⟶
            ShortComplex.π₂).app
            (traceAnalyticStableInfinityCategory
              .cofiberShortComplex morphism₂) =
        (ShortComplex.π₁Toπ₂ :
            (ShortComplex.π₁ :
              ShortComplex StableInfinityOwner.PresentedCategory ⥤
                StableInfinityOwner.PresentedCategory) ⟶
            ShortComplex.π₂).app
            (traceAnalyticStableInfinityCategory
              .cofiberShortComplex morphism₁) ≫
          targetMap ∧
        targetMap ≫
            (ShortComplex.π₂Toπ₃ :
              (ShortComplex.π₂ :
                ShortComplex StableInfinityOwner.PresentedCategory ⥤
                  StableInfinityOwner.PresentedCategory) ⟶
              ShortComplex.π₃).app
              (traceAnalyticStableInfinityCategory
                .cofiberShortComplex morphism₂) =
          (ShortComplex.π₂Toπ₃ :
              (ShortComplex.π₂ :
                ShortComplex StableInfinityOwner.PresentedCategory ⥤
                  StableInfinityOwner.PresentedCategory) ⟶
              ShortComplex.π₃).app
              (traceAnalyticStableInfinityCategory
                .cofiberShortComplex morphism₁) ≫
            traceAnalyticStableInfinityCategory_cofiberComparisonMap
              morphism₁
              morphism₂
              sourceMap
              targetMap
              square ∧
          (traceAnalyticStableInfinityCategory_cofiberComparisonMap
                morphism₁
                morphism₂
                sourceMap
                targetMap
                square)⟦(-1 : ℤ)⟧' ≫
              (ShortComplex.π₁Toπ₂ :
                (ShortComplex.π₁ :
                  ShortComplex StableInfinityOwner.PresentedCategory ⥤
                    StableInfinityOwner.PresentedCategory) ⟶
                ShortComplex.π₂).app
                (traceAnalyticStableInfinityCategory
                  .fiberShortComplex morphism₂) =
            (ShortComplex.π₁Toπ₂ :
                (ShortComplex.π₁ :
                  ShortComplex StableInfinityOwner.PresentedCategory ⥤
                    StableInfinityOwner.PresentedCategory) ⟶
                ShortComplex.π₂).app
                (traceAnalyticStableInfinityCategory
                  .fiberShortComplex morphism₁) ≫
              sourceMap ∧
            sourceMap ≫
                (ShortComplex.π₂Toπ₃ :
                  (ShortComplex.π₂ :
                    ShortComplex StableInfinityOwner.PresentedCategory ⥤
                      StableInfinityOwner.PresentedCategory) ⟶
                  ShortComplex.π₃).app
                  (traceAnalyticStableInfinityCategory
                    .fiberShortComplex morphism₂) =
              (ShortComplex.π₂Toπ₃ :
                  (ShortComplex.π₂ :
                    ShortComplex StableInfinityOwner.PresentedCategory ⥤
                      StableInfinityOwner.PresentedCategory) ⟶
                  ShortComplex.π₃).app
                  (traceAnalyticStableInfinityCategory
                    .fiberShortComplex morphism₁) ≫
                targetMap :=
  fun morphism₁ morphism₂ sourceMap targetMap square =>
    And.intro
      (traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_π₁Toπ₂_naturality
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square)
      (And.intro
        (traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_π₂Toπ₃_naturality
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square)
        (And.intro
          (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_π₁Toπ₂_naturality
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square)
          (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_π₂Toπ₃_naturality
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square)))

end AnalyticMotives
end LFunctions
end Boundary
