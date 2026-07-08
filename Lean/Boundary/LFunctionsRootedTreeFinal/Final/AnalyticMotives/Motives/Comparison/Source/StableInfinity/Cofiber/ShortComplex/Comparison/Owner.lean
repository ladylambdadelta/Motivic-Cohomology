import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.ShortComplex.Comparison.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Cofiber.Comparison.Owner

/-!
# Cofiber short-complex comparisons in the analytic comparison source

This file exposes the short-complex morphism induced by a commutative square
between comparison-source morphisms and records its component equations.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The comparison-source morphism between chosen cofiber short complexes
induced by a commutative square. -/
def stableInfinityCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberShortComplex morphism₁ ⟶
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberShortComplex morphism₂ :=
  traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The first component of the comparison-source cofiber short-complex
comparison is the source map of the original square. -/
theorem stableInfinityCofiberShortComplexComparisonMap_τ₁
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).τ₁ =
      sourceMap :=
  rfl

/-- The second component of the comparison-source cofiber short-complex
comparison is the target map of the original square. -/
theorem stableInfinityCofiberShortComplexComparisonMap_τ₂
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).τ₂ =
      targetMap :=
  rfl

/-- The third component of the comparison-source cofiber short-complex
comparison is the chosen cofiber comparison map. -/
theorem stableInfinityCofiberShortComplexComparisonMap_τ₃
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityCofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).τ₃ =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  rfl

/-- The first short-complex square is the original commutative square in
short-complex orientation. -/
theorem stableInfinityCofiberShortComplexComparisonMap_comm₁₂
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberShortComplex morphism₂).f =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberShortComplex morphism₁).f ≫
        targetMap :=
  (TraceAnalyticDMgmComparisonSource
    .stableInfinityCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₁₂

/-- The second short-complex square is the cofiber cocone compatibility
square in short-complex orientation. -/
theorem stableInfinityCofiberShortComplexComparisonMap_comm₂₃
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    targetMap ≫
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberShortComplex morphism₂).g =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberShortComplex morphism₁).g ≫
        TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square :=
  (TraceAnalyticDMgmComparisonSource
    .stableInfinityCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₂₃

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
