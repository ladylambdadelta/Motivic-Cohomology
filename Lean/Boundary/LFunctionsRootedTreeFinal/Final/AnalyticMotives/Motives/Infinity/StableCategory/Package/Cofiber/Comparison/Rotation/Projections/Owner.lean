import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Rotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Rotation.Projections.Owner

/-!
# Package-level projection functors on rotated cofiber comparisons

This owner file exposes through `traceAnalyticStableInfinityCategory` the
images of rotated and inverse-rotated cofiber-comparison morphisms under the
three triangle projection functors.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first triangle projection sends the package-level rotated cofiber
comparison to the target map. -/
theorem
    traceAnalyticStableInfinityCategory_triangleFirstProjection_map_rotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.triangleFirstProjection.map
        (traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      targetMap :=
  rfl

/-- The second triangle projection sends the package-level rotated cofiber
comparison to the induced cofiber comparison map. -/
theorem
    traceAnalyticStableInfinityCategory_triangleSecondProjection_map_rotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.triangleSecondProjection.map
        (traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      traceAnalyticStableInfinityCategory_cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The third triangle projection sends the package-level rotated cofiber
comparison to the shifted source map. -/
theorem
    traceAnalyticStableInfinityCategory_triangleThirdProjection_map_rotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.triangleThirdProjection.map
        (traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      sourceMap⟦(1 : ℤ)⟧' :=
  rfl

/-- The first triangle projection sends the package-level inverse-rotated
cofiber comparison to the shifted cofiber comparison map. -/
theorem
    traceAnalyticStableInfinityCategory_triangleFirstProjection_map_invRotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.triangleFirstProjection.map
        (traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap
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

/-- The second triangle projection sends the package-level inverse-rotated
cofiber comparison to the source map. -/
theorem
    traceAnalyticStableInfinityCategory_triangleSecondProjection_map_invRotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.triangleSecondProjection.map
        (traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      sourceMap :=
  rfl

/-- The third triangle projection sends the package-level inverse-rotated
cofiber comparison to the target map. -/
theorem
    traceAnalyticStableInfinityCategory_triangleThirdProjection_map_invRotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.triangleThirdProjection.map
        (traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap
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
