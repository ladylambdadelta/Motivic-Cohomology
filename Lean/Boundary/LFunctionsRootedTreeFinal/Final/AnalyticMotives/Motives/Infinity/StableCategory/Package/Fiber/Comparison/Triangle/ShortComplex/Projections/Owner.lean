import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Fiber.Comparison.Triangle.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Fiber.Comparison.Triangle.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Fiber.Comparison.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Comparison.Triangle.ShortComplex.Projections.Owner

/-!
# Package-level projection compatibility for fiber comparisons

This owner file exposes through `traceAnalyticStableInfinityCategory` that
projecting the fiber short-complex comparison agrees with projecting the
corresponding fiber triangle comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Package-level first projection compatibility between fiber short-complex
and triangle comparison morphisms. -/
theorem
    traceAnalyticStableInfinityCategory_fiberComparison_shortComplexFirstProjection_eq_triangleFirstProjection
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
        (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      traceAnalyticStableInfinityCategory.triangleFirstProjection.map
        (traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

/-- Package-level second projection compatibility between fiber short-complex
and triangle comparison morphisms. -/
theorem
    traceAnalyticStableInfinityCategory_fiberComparison_shortComplexSecondProjection_eq_triangleSecondProjection
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
        (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      traceAnalyticStableInfinityCategory.triangleSecondProjection.map
        (traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

/-- Package-level third projection compatibility between fiber short-complex
and triangle comparison morphisms. -/
theorem
    traceAnalyticStableInfinityCategory_fiberComparison_shortComplexThirdProjection_eq_triangleThirdProjection
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
        (traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      traceAnalyticStableInfinityCategory.triangleThirdProjection.map
        (traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
