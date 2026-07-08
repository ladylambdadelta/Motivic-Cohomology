import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.CofiberRotations.Comparison.Projections.Owner

/-!
# Naturality of short-complex projections for rotated cofiber comparisons

This owner file states the naturality squares for rotated and inverse-rotated
cofiber short-complex comparison morphisms with respect to Mathlib's natural
transformations `ShortComplex.π₁Toπ₂` and `ShortComplex.π₂Toπ₃`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Naturality of `ShortComplex.π₁Toπ₂` at the rotated cofiber
short-complex comparison morphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplexComparisonMap_π₁Toπ₂_naturality
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
          (TraceAnalyticStableMotiveQuasicategory
            .rotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₂).app
          (TraceAnalyticStableMotiveQuasicategory
            .rotatedCofiberShortComplex morphism₁) ≫
        TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  (TraceAnalyticStableMotiveQuasicategory
    .rotatedCofiberShortComplexComparisonMap_comm₁₂
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

/-- Naturality of `ShortComplex.π₂Toπ₃` at the rotated cofiber
short-complex comparison morphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplexComparisonMap_π₂Toπ₃_naturality
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
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
          (TraceAnalyticStableMotiveQuasicategory
            .rotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₃).app
          (TraceAnalyticStableMotiveQuasicategory
            .rotatedCofiberShortComplex morphism₁) ≫
        sourceMap⟦(1 : ℤ)⟧' :=
  (TraceAnalyticStableMotiveQuasicategory
    .rotatedCofiberShortComplexComparisonMap_comm₂₃
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

/-- Naturality of `ShortComplex.π₁Toπ₂` at the inverse-rotated cofiber
short-complex comparison morphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplexComparisonMap_π₁Toπ₂_naturality
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
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
          (TraceAnalyticStableMotiveQuasicategory
            .invRotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₂).app
          (TraceAnalyticStableMotiveQuasicategory
            .invRotatedCofiberShortComplex morphism₁) ≫
        sourceMap :=
  (TraceAnalyticStableMotiveQuasicategory
    .invRotatedCofiberShortComplexComparisonMap_comm₁₂
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

/-- Naturality of `ShortComplex.π₂Toπ₃` at the inverse-rotated cofiber
short-complex comparison morphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplexComparisonMap_π₂Toπ₃_naturality
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
          (TraceAnalyticStableMotiveQuasicategory
            .invRotatedCofiberShortComplex morphism₂) =
      (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₃).app
          (TraceAnalyticStableMotiveQuasicategory
            .invRotatedCofiberShortComplex morphism₁) ≫
        targetMap :=
  (TraceAnalyticStableMotiveQuasicategory
    .invRotatedCofiberShortComplexComparisonMap_comm₂₃
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

end AnalyticMotives
end LFunctions
end Boundary
