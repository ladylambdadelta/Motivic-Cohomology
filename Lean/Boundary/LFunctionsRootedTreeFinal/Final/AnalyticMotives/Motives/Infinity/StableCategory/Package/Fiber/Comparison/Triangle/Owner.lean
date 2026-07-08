import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Rotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Fiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Comparison.Triangle.Owner

/-!
# Package-level fiber-triangle comparison morphisms

This owner file exposes through `traceAnalyticStableInfinityCategory` the
fiber-triangle comparison morphism induced by a commutative square.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level morphism between chosen fiber triangles induced by a
commutative square. -/
def traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.fiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.fiberTriangle morphism₂ :=
  traceAnalyticStableInfinityCategory.fiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The package-level fiber-triangle comparison is the inverse-rotated
cofiber-triangle comparison. -/
theorem
    traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap_eq_invRotatedCofiber
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The first component of the package-level fiber-triangle comparison is the
desuspended package-level cofiber comparison map. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap_hom₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₁ =
      (traceAnalyticStableInfinityCategory_cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square)⟦(-1 : ℤ)⟧' :=
  rfl

/-- The second component of the package-level fiber-triangle comparison is
the source map of the original commutative square. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap_hom₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₂ =
      sourceMap :=
  rfl

/-- The third component of the package-level fiber-triangle comparison is the
target map of the original commutative square. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap_hom₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₃ =
      targetMap :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
