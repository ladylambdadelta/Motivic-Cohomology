import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.CofiberRotations.Comparison.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.CofiberRotations.Comparison.Projections.Naturality.Owner

/-!
# Package-level naturality for rotated cofiber short-complex comparisons

This owner file exposes through `traceAnalyticStableInfinityCategory` the
naturality squares for rotated and inverse-rotated cofiber short-complex
comparison morphisms with respect to `ShortComplex.π₁Toπ₂` and
`ShortComplex.π₂Toπ₃`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Package-level naturality of `ShortComplex.π₁Toπ₂` at the rotated
cofiber short-complex comparison morphism. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_π₁Toπ₂_naturality
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
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
          square :=
  (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_comm₁₂
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

/-- Package-level naturality of `ShortComplex.π₂Toπ₃` at the rotated
cofiber short-complex comparison morphism. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_π₂Toπ₃_naturality
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
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
        sourceMap⟦(1 : ℤ)⟧' :=
  (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap_comm₂₃
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

/-- Package-level naturality of `ShortComplex.π₁Toπ₂` at the
inverse-rotated cofiber short-complex comparison morphism. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_π₁Toπ₂_naturality
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
            .invRotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₂).app
          (traceAnalyticStableInfinityCategory
            .invRotatedCofiberShortComplex morphism₁) ≫
        sourceMap :=
  (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_comm₁₂
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

/-- Package-level naturality of `ShortComplex.π₂Toπ₃` at the
inverse-rotated cofiber short-complex comparison morphism. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_π₂Toπ₃_naturality
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
            .invRotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₃).app
          (traceAnalyticStableInfinityCategory
            .invRotatedCofiberShortComplex morphism₁) ≫
        targetMap :=
  (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap_comm₂₃
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

end AnalyticMotives
end LFunctions
end Boundary
