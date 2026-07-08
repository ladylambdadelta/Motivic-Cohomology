import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Rotation.Owner

/-!
# Projection functors on rotated cofiber-comparison morphisms

This owner file identifies the images of rotated and inverse-rotated
cofiber-comparison morphisms under the three triangle projection functors.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first triangle projection sends the rotated cofiber comparison to the
target map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .triangleFirstProjection_map_rotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.triangleFirstProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .rotatedCofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      targetMap :=
  rfl

/-- The second triangle projection sends the rotated cofiber comparison to the
induced cofiber comparison map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .triangleSecondProjection_map_rotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.triangleSecondProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .rotatedCofiberTriangleComparisonMap
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

/-- The third triangle projection sends the rotated cofiber comparison to the
shifted source map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .triangleThirdProjection_map_rotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.triangleThirdProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .rotatedCofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      sourceMap⟦(1 : ℤ)⟧' :=
  rfl

/-- The first triangle projection sends the inverse-rotated cofiber comparison
to the shifted cofiber comparison map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .triangleFirstProjection_map_invRotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.triangleFirstProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .invRotatedCofiberTriangleComparisonMap
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

/-- The second triangle projection sends the inverse-rotated cofiber comparison
to the source map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .triangleSecondProjection_map_invRotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.triangleSecondProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .invRotatedCofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      sourceMap :=
  rfl

/-- The third triangle projection sends the inverse-rotated cofiber comparison
to the target map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .triangleThirdProjection_map_invRotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.triangleThirdProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .invRotatedCofiberTriangleComparisonMap
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
