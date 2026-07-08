import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.ShortComplex.Rotations.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.Comparison.Triangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Fiber.Comparison.Triangle.Owner

/-!
# Fiber-triangle comparisons in the analytic comparison source

This file exposes the stable-infinity fiber-triangle comparison morphism
induced by a commutative square of comparison-source morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The comparison-source morphism between chosen stable-infinity fiber
triangles induced by a commutative square. -/
def stableInfinityFiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangle morphism₁ ⟶
      TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangle morphism₂ :=
  traceAnalyticStableInfinityCategory_fiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The comparison-source fiber-triangle comparison is the inverse-rotated
cofiber-triangle comparison. -/
theorem stableInfinityFiberTriangleComparisonMap_eq_invRotatedCofiber
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.invRotatedCofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  rfl

/-- The first component of the comparison-source fiber-triangle comparison is
the deshifted cofiber comparison map. -/
theorem stableInfinityFiberTriangleComparisonMap_hom₁
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).hom₁ =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square)⟦(-1 : ℤ)⟧' :=
  rfl

/-- The second component of the comparison-source fiber-triangle comparison
is the source map of the original square. -/
theorem stableInfinityFiberTriangleComparisonMap_hom₂
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).hom₂ =
      sourceMap :=
  rfl

/-- The third component of the comparison-source fiber-triangle comparison is
the target map of the original square. -/
theorem stableInfinityFiberTriangleComparisonMap_hom₃
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityFiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).hom₃ =
      targetMap :=
  rfl

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
