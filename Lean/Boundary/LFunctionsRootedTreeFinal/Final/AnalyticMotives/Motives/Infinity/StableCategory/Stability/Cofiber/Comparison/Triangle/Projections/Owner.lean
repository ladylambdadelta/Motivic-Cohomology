import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Triangle.Owner

/-!
# Projection functors on cofiber-comparison triangle morphisms

This owner file identifies the images of the cofiber-comparison triangle
morphism under the three vertex projection functors.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first triangle projection sends the cofiber triangle comparison to the
source map of the original commutative square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .triangleFirstProjection_map_cofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.triangleFirstProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .cofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      sourceMap :=
  rfl

/-- The second triangle projection sends the cofiber triangle comparison to
the target map of the original commutative square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .triangleSecondProjection_map_cofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.triangleSecondProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .cofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      targetMap :=
  rfl

/-- The third triangle projection sends the cofiber triangle comparison to
the induced cofiber comparison map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .triangleThirdProjection_map_cofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.triangleThirdProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .cofiberTriangleComparisonMap
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

end AnalyticMotives
end LFunctions
end Boundary
