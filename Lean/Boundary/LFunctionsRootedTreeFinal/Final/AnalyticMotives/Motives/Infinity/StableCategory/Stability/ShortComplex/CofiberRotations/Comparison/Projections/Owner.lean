import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.CofiberRotations.Comparison.Owner

/-!
# Projection functors on rotated cofiber short-complex comparisons

This owner file identifies the images of the rotated and inverse-rotated
cofiber short-complex comparison morphisms under the three short-complex
projection functors.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first short-complex projection sends the rotated cofiber
short-complex comparison to the target map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .shortComplexFirstProjection_map_rotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (ShortComplex.π₁ :
        ShortComplex StableInfinityOwner.PresentedCategory ⥤
          StableInfinityOwner.PresentedCategory).map
        (TraceAnalyticStableMotiveQuasicategory
          .rotatedCofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      targetMap :=
  rfl

/-- The second short-complex projection sends the rotated cofiber
short-complex comparison to the induced cofiber comparison map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .shortComplexSecondProjection_map_rotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (ShortComplex.π₂ :
        ShortComplex StableInfinityOwner.PresentedCategory ⥤
          StableInfinityOwner.PresentedCategory).map
        (TraceAnalyticStableMotiveQuasicategory
          .rotatedCofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The third short-complex projection sends the rotated cofiber
short-complex comparison to the shifted source map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .shortComplexThirdProjection_map_rotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (ShortComplex.π₃ :
        ShortComplex StableInfinityOwner.PresentedCategory ⥤
          StableInfinityOwner.PresentedCategory).map
        (TraceAnalyticStableMotiveQuasicategory
          .rotatedCofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      sourceMap⟦(1 : ℤ)⟧' :=
  rfl

/-- The first short-complex projection sends the inverse-rotated cofiber
short-complex comparison to the desuspended cofiber comparison map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .shortComplexFirstProjection_map_invRotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (ShortComplex.π₁ :
        ShortComplex StableInfinityOwner.PresentedCategory ⥤
          StableInfinityOwner.PresentedCategory).map
        (TraceAnalyticStableMotiveQuasicategory
          .invRotatedCofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      (TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square)⟦(-1 : ℤ)⟧' :=
  rfl

/-- The second short-complex projection sends the inverse-rotated cofiber
short-complex comparison to the source map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .shortComplexSecondProjection_map_invRotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (ShortComplex.π₂ :
        ShortComplex StableInfinityOwner.PresentedCategory ⥤
          StableInfinityOwner.PresentedCategory).map
        (TraceAnalyticStableMotiveQuasicategory
          .invRotatedCofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      sourceMap :=
  rfl

/-- The third short-complex projection sends the inverse-rotated cofiber
short-complex comparison to the target map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .shortComplexThirdProjection_map_invRotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (ShortComplex.π₃ :
        ShortComplex StableInfinityOwner.PresentedCategory ⥤
          StableInfinityOwner.PresentedCategory).map
        (TraceAnalyticStableMotiveQuasicategory
          .invRotatedCofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      targetMap :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
