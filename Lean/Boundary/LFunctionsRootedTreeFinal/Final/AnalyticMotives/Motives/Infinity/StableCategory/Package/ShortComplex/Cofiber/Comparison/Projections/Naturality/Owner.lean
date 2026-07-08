import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Cofiber.Comparison.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Cofiber.Comparison.Projections.Naturality.Owner

/-!
# Package-level naturality of short-complex projections for cofiber comparisons

This owner file exposes through `traceAnalyticStableInfinityCategory` the two
naturality squares for the cofiber short-complex comparison morphism with
respect to `ShortComplex.π₁Toπ₂` and `ShortComplex.π₂Toπ₃`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Package-level naturality of `ShortComplex.π₁Toπ₂` at the cofiber
short-complex comparison morphism. -/
theorem
    traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_π₁Toπ₂_naturality
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
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
        targetMap :=
  (traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_comm₁₂
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

/-- Package-level naturality of `ShortComplex.π₂Toπ₃` at the cofiber
short-complex comparison morphism. -/
theorem
    traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_π₂Toπ₃_naturality
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
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
          square :=
  (traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap_comm₂₃
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

end AnalyticMotives
end LFunctions
end Boundary
