import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Fiber.Comparison.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Fiber.Comparison.Projections.Naturality.Owner

/-!
# Package-level naturality of short-complex projections for fiber comparisons

This owner file exposes through `traceAnalyticStableInfinityCategory` the two
naturality squares for the fiber short-complex comparison morphism with
respect to `ShortComplex.π₁Toπ₂` and `ShortComplex.π₂Toπ₃`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Package-level naturality of `ShortComplex.π₁Toπ₂` at the fiber
short-complex comparison morphism. -/
theorem
    traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_π₁Toπ₂_naturality
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
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
        sourceMap :=
  (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_comm₁₂
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

/-- Package-level naturality of `ShortComplex.π₂Toπ₃` at the fiber
short-complex comparison morphism. -/
theorem
    traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_π₂Toπ₃_naturality
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
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
  (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_comm₂₃
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

end AnalyticMotives
end LFunctions
end Boundary
