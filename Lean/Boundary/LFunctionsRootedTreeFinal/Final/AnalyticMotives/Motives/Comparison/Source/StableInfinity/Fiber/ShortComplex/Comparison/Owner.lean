import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.ShortComplex.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Fiber.ShortComplex.Comparison.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Fiber.Comparison.Owner

/-!
# Fiber short-complex comparisons in the analytic comparison source

This file exposes the short-complex morphism induced on chosen fiber short
complexes by a commutative square between comparison-source morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The comparison-source morphism between chosen fiber short complexes
induced by a commutative square. -/
def stableInfinityFiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberShortComplex morphism₁ ⟶
      TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberShortComplex morphism₂ :=
  traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The first component of the comparison-source fiber short-complex
comparison is the deshifted chosen cofiber comparison map. -/
theorem stableInfinityFiberShortComplexComparisonMap_τ₁
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
        .stableInfinityCofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square)⟦(-1 : ℤ)⟧' :=
  rfl

/-- The second component of the comparison-source fiber short-complex
comparison is the source map of the original square. -/
theorem stableInfinityFiberShortComplexComparisonMap_τ₂
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
      sourceMap :=
  rfl

/-- The third component of the comparison-source fiber short-complex
comparison is the target map of the original square. -/
theorem stableInfinityFiberShortComplexComparisonMap_τ₃
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
      targetMap :=
  rfl

/-- The first short-complex square is the fiber-map compatibility square. -/
theorem stableInfinityFiberShortComplexComparisonMap_comm₁₂
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square)⟦(-1 : ℤ)⟧' ≫
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityFiberShortComplex morphism₂).f =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberShortComplex morphism₁).f ≫
        sourceMap :=
  (TraceAnalyticDMgmComparisonSource
    .stableInfinityFiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₁₂

/-- The second short-complex square is the original commutative square in
short-complex orientation. -/
theorem stableInfinityFiberShortComplexComparisonMap_comm₂₃
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityFiberShortComplex morphism₂).g =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityFiberShortComplex morphism₁).g ≫
        targetMap :=
  (TraceAnalyticDMgmComparisonSource
    .stableInfinityFiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₂₃

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
