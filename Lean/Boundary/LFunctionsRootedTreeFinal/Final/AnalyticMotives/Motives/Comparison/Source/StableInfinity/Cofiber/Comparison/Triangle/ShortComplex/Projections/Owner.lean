import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Comparison.Triangle.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Triangle.ShortComplex.Projections.Owner

/-!
# Projection compatibility for cofiber comparison morphisms

This file exposes in the comparison-source namespace that projecting the
cofiber short-complex comparison agrees with projecting the corresponding
cofiber triangle comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The first projection of the cofiber short-complex comparison agrees with
the first projection of the cofiber triangle comparison. -/
theorem
    stableInfinityCofiberComparison_shortComplexFirstProjection_eq_triangleFirstProjection
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
          .stableInfinityCofiberShortComplexComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square) =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.triangleFirstProjection.map
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberTriangleComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square) :=
  rfl

/-- The second projection of the cofiber short-complex comparison agrees with
the second projection of the cofiber triangle comparison. -/
theorem
    stableInfinityCofiberComparison_shortComplexSecondProjection_eq_triangleSecondProjection
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
          .stableInfinityCofiberShortComplexComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square) =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.triangleSecondProjection.map
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberTriangleComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square) :=
  rfl

/-- The third projection of the cofiber short-complex comparison agrees with
the third projection of the cofiber triangle comparison. -/
theorem
    stableInfinityCofiberComparison_shortComplexThirdProjection_eq_triangleThirdProjection
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
          .stableInfinityCofiberShortComplexComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square) =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.triangleThirdProjection.map
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberTriangleComparisonMap
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
