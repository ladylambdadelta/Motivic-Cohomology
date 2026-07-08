import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.CofiberRotations.Comparison.Projections.Naturality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Comparison.Naturality.Owner

/-!
# Global naturality certificate for rotated cofiber comparison short complexes

This file bundles the naturality laws for rotated and inverse-rotated cofiber
short-complex comparison maps attached to a commutative square in the concrete
analytic stable category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The global comparison package is natural for the two structure maps of
the rotated and inverse-rotated cofiber short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_global_comparison_rotation_naturality :
    ∀ {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
      (morphism₁ : source₁ ⟶ target₁)
      (morphism₂ : source₂ ⟶ target₂)
      (sourceMap : source₁ ⟶ source₂)
      (targetMap : target₁ ⟶ target₂)
      (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂),
      targetMap ≫
          (ShortComplex.π₁Toπ₂ :
            (ShortComplex.π₁ :
              ShortComplex StableInfinityOwner.PresentedCategory ⥤
                StableInfinityOwner.PresentedCategory) ⟶
            ShortComplex.π₂).app
            (traceAnalyticStableInfinityCategory
              .rotatedCofiberShortComplex morphism₂) =
        (ShortComplex.π₁Toπ₂ :
            (ShortComplex.π₁ :
              ShortComplex StableInfinityOwner.PresentedCategory ⥤
                StableInfinityOwner.PresentedCategory) ⟶
            ShortComplex.π₂).app
            (traceAnalyticStableInfinityCategory
              .rotatedCofiberShortComplex morphism₁) ≫
          traceAnalyticStableInfinityCategory_cofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square ∧
        traceAnalyticStableInfinityCategory_cofiberComparisonMap
              morphism₁
              morphism₂
              sourceMap
              targetMap
              square ≫
            (ShortComplex.π₂Toπ₃ :
              (ShortComplex.π₂ :
                ShortComplex StableInfinityOwner.PresentedCategory ⥤
                  StableInfinityOwner.PresentedCategory) ⟶
              ShortComplex.π₃).app
              (traceAnalyticStableInfinityCategory
                .rotatedCofiberShortComplex morphism₂) =
          (ShortComplex.π₂Toπ₃ :
              (ShortComplex.π₂ :
                ShortComplex StableInfinityOwner.PresentedCategory ⥤
                  StableInfinityOwner.PresentedCategory) ⟶
              ShortComplex.π₃).app
              (traceAnalyticStableInfinityCategory
                .rotatedCofiberShortComplex morphism₁) ≫
            sourceMap⟦(1 : ℤ)⟧' ∧
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
                  .invRotatedCofiberShortComplex morphism₂) =
            (ShortComplex.π₁Toπ₂ :
                (ShortComplex.π₁ :
                  ShortComplex StableInfinityOwner.PresentedCategory ⥤
                    StableInfinityOwner.PresentedCategory) ⟶
                ShortComplex.π₂).app
                (traceAnalyticStableInfinityCategory
                  .invRotatedCofiberShortComplex morphism₁) ≫
              sourceMap ∧
            sourceMap ≫
                (ShortComplex.π₂Toπ₃ :
                  (ShortComplex.π₂ :
                    ShortComplex StableInfinityOwner.PresentedCategory ⥤
                      StableInfinityOwner.PresentedCategory) ⟶
                  ShortComplex.π₃).app
                  (traceAnalyticStableInfinityCategory
                    .invRotatedCofiberShortComplex morphism₂) =
              (ShortComplex.π₂Toπ₃ :
                  (ShortComplex.π₂ :
                    ShortComplex StableInfinityOwner.PresentedCategory ⥤
                      StableInfinityOwner.PresentedCategory) ⟶
                  ShortComplex.π₃).app
                  (traceAnalyticStableInfinityCategory
                    .invRotatedCofiberShortComplex morphism₁) ≫
                targetMap :=
  fun morphism₁ morphism₂ sourceMap targetMap square =>
    And.intro
      (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_π₁Toπ₂_naturality
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square)
      (And.intro
        (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_π₂Toπ₃_naturality
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square)
        (And.intro
          (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_π₁Toπ₂_naturality
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square)
          (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_π₂Toπ₃_naturality
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square)))

end AnalyticMotives
end LFunctions
end Boundary
