import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.Comparison.Triangle.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Fiber.Comparison.Triangle.ShortComplex.Projections.Owner

/-!
# Projection compatibility for fiber comparison morphisms

This file exposes in the comparison-source namespace that projecting the
fiber short-complex comparison agrees with projecting the corresponding fiber
triangle comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The first projection of the fiber short-complex comparison agrees with
the first projection of the fiber triangle comparison. -/
theorem
    stableInfinityFiberComparison_shortComplexFirstProjection_eq_triangleFirstProjection
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (ShortComplex.π₁ :
        ShortComplex TraceAnalyticDMgmComparisonSource ⥤
          TraceAnalyticDMgmComparisonSource).map
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityFiberShortComplexComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square) =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.triangleFirstProjection.map
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityFiberTriangleComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square) :=
  rfl

/-- The second projection of the fiber short-complex comparison agrees with
the second projection of the fiber triangle comparison. -/
theorem
    stableInfinityFiberComparison_shortComplexSecondProjection_eq_triangleSecondProjection
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (ShortComplex.π₂ :
        ShortComplex TraceAnalyticDMgmComparisonSource ⥤
          TraceAnalyticDMgmComparisonSource).map
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityFiberShortComplexComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square) =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.triangleSecondProjection.map
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityFiberTriangleComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square) :=
  rfl

/-- The third projection of the fiber short-complex comparison agrees with
the third projection of the fiber triangle comparison. -/
theorem
    stableInfinityFiberComparison_shortComplexThirdProjection_eq_triangleThirdProjection
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (ShortComplex.π₃ :
        ShortComplex TraceAnalyticDMgmComparisonSource ⥤
          TraceAnalyticDMgmComparisonSource).map
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityFiberShortComplexComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square) =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.triangleThirdProjection.map
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityFiberTriangleComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square) :=
  rfl

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
