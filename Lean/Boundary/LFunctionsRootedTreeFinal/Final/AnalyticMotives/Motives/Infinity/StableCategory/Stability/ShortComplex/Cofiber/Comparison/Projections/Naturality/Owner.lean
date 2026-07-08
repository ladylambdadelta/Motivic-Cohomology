import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Cofiber.Comparison.Projections.Owner

/-!
# Naturality of short-complex projections for cofiber comparisons

This owner file states the two naturality squares for the cofiber
short-complex comparison morphism with respect to Mathlib's natural
transformations `ShortComplex.π₁Toπ₂` and `ShortComplex.π₂Toπ₃`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Naturality of `ShortComplex.π₁Toπ₂` at the cofiber short-complex
comparison morphism recovers the original commutative square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap_π₁Toπ₂_naturality
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
          (TraceAnalyticStableMotiveQuasicategory
            .cofiberShortComplex morphism₂) =
      (ShortComplex.π₁Toπ₂ :
          (ShortComplex.π₁ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₂).app
          (TraceAnalyticStableMotiveQuasicategory
            .cofiberShortComplex morphism₁) ≫
        targetMap :=
  (TraceAnalyticStableMotiveQuasicategory
    .cofiberShortComplexComparisonMap_comm₁₂
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

/-- Naturality of `ShortComplex.π₂Toπ₃` at the cofiber short-complex
comparison morphism recovers the cocone compatibility square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap_π₂Toπ₃_naturality
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
          (TraceAnalyticStableMotiveQuasicategory
            .cofiberShortComplex morphism₂) =
      (ShortComplex.π₂Toπ₃ :
          (ShortComplex.π₂ :
            ShortComplex StableInfinityOwner.PresentedCategory ⥤
              StableInfinityOwner.PresentedCategory) ⟶
          ShortComplex.π₃).app
          (TraceAnalyticStableMotiveQuasicategory
            .cofiberShortComplex morphism₁) ≫
        TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  (TraceAnalyticStableMotiveQuasicategory
    .cofiberShortComplexComparisonMap_comm₂₃
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square)

end AnalyticMotives
end LFunctions
end Boundary
