import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.ShortComplex.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Fiber.Comparison.Triangle.ShortComplex.Owner

/-!
# Fiber triangle and short-complex comparison compatibility

This file exposes in the comparison-source namespace that the fiber
short-complex comparison and fiber triangle comparison induced by the same
commutative square have the same three underlying component maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The first component of the fiber short-complex comparison is the first
component of the fiber triangle comparison. -/
theorem stableInfinityFiberShortComplexComparisonMap_τ₁_eq_triangle_hom₁
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).τ₁ =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square).hom₁ :=
  rfl

/-- The second component of the fiber short-complex comparison is the second
component of the fiber triangle comparison. -/
theorem stableInfinityFiberShortComplexComparisonMap_τ₂_eq_triangle_hom₂
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).τ₂ =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square).hom₂ :=
  rfl

/-- The third component of the fiber short-complex comparison is the third
component of the fiber triangle comparison. -/
theorem stableInfinityFiberShortComplexComparisonMap_τ₃_eq_triangle_hom₃
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).τ₃ =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square).hom₃ :=
  rfl

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
