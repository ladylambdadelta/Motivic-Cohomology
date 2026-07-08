import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Fiber.Comparison.Triangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Fiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Comparison.Triangle.ShortComplex.Owner

/-!
# Package-level compatibility of fiber triangle and short-complex comparisons

This owner file exposes through `traceAnalyticStableInfinityCategory` that the
fiber triangle comparison morphism and fiber short-complex comparison morphism
induced by the same commutative square have the same three underlying maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first component of the package-level fiber short-complex comparison
is the first component of the package-level fiber triangle comparison. -/
theorem
    traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_τ₁_eq_triangle_hom₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₁ =
      (traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).hom₁ :=
  rfl

/-- The second component of the package-level fiber short-complex comparison
is the second component of the package-level fiber triangle comparison. -/
theorem
    traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_τ₂_eq_triangle_hom₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₂ =
      (traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).hom₂ :=
  rfl

/-- The third component of the package-level fiber short-complex comparison
is the third component of the package-level fiber triangle comparison. -/
theorem
    traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap_τ₃_eq_triangle_hom₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₃ =
      (traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).hom₃ :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
