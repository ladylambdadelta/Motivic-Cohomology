import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.Comparison.Triangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Triangle.Owner

/-!
# Cofiber-triangle comparisons in the analytic comparison source

This file exposes the stable-infinity cofiber-triangle comparison morphism for
commutative squares of analytic comparison-source morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The comparison-source map between chosen stable-infinity cofiber objects
induced by a commutative square. -/
def stableInfinityCofiberComparisonMap
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberObject morphism₁ ⟶
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberObject morphism₂ :=
  traceAnalyticStableInfinityCategory_cofiberComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The comparison-source morphism between chosen stable-infinity cofiber
triangles induced by a commutative square. -/
def stableInfinityCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle morphism₁ ⟶
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberTriangle morphism₂ :=
  traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The first component of the comparison-source cofiber-triangle comparison
is the source map of the original commutative square. -/
theorem stableInfinityCofiberTriangleComparisonMap_hom₁
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).hom₁ =
      sourceMap :=
  rfl

/-- The second component of the comparison-source cofiber-triangle comparison
is the target map of the original commutative square. -/
theorem stableInfinityCofiberTriangleComparisonMap_hom₂
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).hom₂ =
      targetMap :=
  rfl

/-- The third component of the comparison-source cofiber-triangle comparison
is the chosen comparison-source cofiber comparison map. -/
theorem stableInfinityCofiberTriangleComparisonMap_hom₃
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).hom₃ =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  rfl

/-- The first square of the comparison-source cofiber-triangle comparison is
the original commutative square. -/
theorem stableInfinityCofiberTriangleComparisonMap_comm₁
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle morphism₁).mor₁ ≫ targetMap =
      sourceMap ≫
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberTriangle morphism₂).mor₁ :=
  (TraceAnalyticDMgmComparisonSource
    .stableInfinityCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₁

/-- The comparison-source cofiber comparison map makes the cocone square
commute. -/
theorem stableInfinityCofiberComparisonMap_cocone
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberCoconeMap morphism₁ ≫
        TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square =
      targetMap ≫
        TraceAnalyticDMgmComparisonSource
          .stableInfinityCategory.cofiberCoconeMap morphism₂ :=
  traceAnalyticStableInfinityCategory_cofiberComparisonMap_cocone
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The comparison-source cofiber comparison map makes the boundary square
commute. -/
theorem stableInfinityCofiberComparisonMap_boundary
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCategory.cofiberBoundary morphism₁ ≫
        sourceMap⟦(1 : ℤ)⟧' =
      TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square ≫
        TraceAnalyticDMgmComparisonSource
          .stableInfinityCategory.cofiberBoundary morphism₂ :=
  traceAnalyticStableInfinityCategory_cofiberComparisonMap_boundary
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The second square of the comparison-source cofiber-triangle comparison is
the cocone compatibility square. -/
theorem stableInfinityCofiberTriangleComparisonMap_comm₂
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle morphism₁).mor₂ ≫
        TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square =
      targetMap ≫
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberTriangle morphism₂).mor₂ :=
  (TraceAnalyticDMgmComparisonSource
    .stableInfinityCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₂

/-- The third square of the comparison-source cofiber-triangle comparison is
the boundary compatibility square. -/
theorem stableInfinityCofiberTriangleComparisonMap_comm₃
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberTriangle morphism₁).mor₃ ≫
        sourceMap⟦(1 : ℤ)⟧' =
      TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square ≫
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberTriangle morphism₂).mor₃ :=
  (TraceAnalyticDMgmComparisonSource
    .stableInfinityCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₃

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
