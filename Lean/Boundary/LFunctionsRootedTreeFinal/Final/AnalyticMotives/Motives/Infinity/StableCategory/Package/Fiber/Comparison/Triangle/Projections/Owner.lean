import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Fiber.Comparison.Triangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Comparison.Triangle.Projections.Owner

/-!
# Package-level projections on fiber-triangle comparison morphisms

This owner file exposes through `traceAnalyticStableInfinityCategory` the
images of the fiber-triangle comparison morphism under the three package
vertex projection functors.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level first triangle projection sends the fiber-triangle
comparison to the desuspended cofiber comparison map. -/
theorem
    traceAnalyticStableInfinityCategory_triangleFirstProjection_map_fiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.triangleFirstProjection.map
        (traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      (traceAnalyticStableInfinityCategory_cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square)⟦(-1 : ℤ)⟧' :=
  rfl

/-- The package-level second triangle projection sends the fiber-triangle
comparison to the source map of the original commutative square. -/
theorem
    traceAnalyticStableInfinityCategory_triangleSecondProjection_map_fiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.triangleSecondProjection.map
        (traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      sourceMap :=
  rfl

/-- The package-level third triangle projection sends the fiber-triangle
comparison to the target map of the original commutative square. -/
theorem
    traceAnalyticStableInfinityCategory_triangleThirdProjection_map_fiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.triangleThirdProjection.map
        (traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
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
