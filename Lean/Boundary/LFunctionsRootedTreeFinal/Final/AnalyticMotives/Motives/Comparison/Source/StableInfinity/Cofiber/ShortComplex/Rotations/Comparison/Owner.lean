import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.ShortComplex.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.ShortComplex.Rotations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Cofiber.ShortComplex.Rotations.Comparison.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.CofiberRotations.Comparison.Owner

/-!
# Rotated cofiber short-complex comparisons in the comparison source

This file exposes the comparison morphisms between rotated and inverse-rotated
cofiber short complexes induced by a commutative square.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The comparison-source morphism between rotated cofiber short complexes
induced by a commutative square. -/
def stableInfinityRotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityRotatedCofiberShortComplex morphism₁ ⟶
      TraceAnalyticDMgmComparisonSource
        .stableInfinityRotatedCofiberShortComplex morphism₂ :=
  traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The comparison-source morphism between inverse-rotated cofiber short
complexes induced by a commutative square. -/
def stableInfinityInvRotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityInvRotatedCofiberShortComplex morphism₁ ⟶
      TraceAnalyticDMgmComparisonSource
        .stableInfinityInvRotatedCofiberShortComplex morphism₂ :=
  traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The first component of the rotated cofiber short-complex comparison is
the target map. -/
theorem stableInfinityRotatedCofiberShortComplexComparisonMap_τ₁
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityRotatedCofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).τ₁ =
      targetMap :=
  rfl

/-- The second component of the rotated cofiber short-complex comparison is
the chosen cofiber comparison map. -/
theorem stableInfinityRotatedCofiberShortComplexComparisonMap_τ₂
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityRotatedCofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).τ₂ =
      TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  rfl

/-- The third component of the rotated cofiber short-complex comparison is
the shifted source map. -/
theorem stableInfinityRotatedCofiberShortComplexComparisonMap_τ₃
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityRotatedCofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).τ₃ =
      sourceMap⟦(1 : ℤ)⟧' :=
  rfl

/-- The first component of the inverse-rotated cofiber short-complex
comparison is the deshifted cofiber comparison map. -/
theorem stableInfinityInvRotatedCofiberShortComplexComparisonMap_τ₁
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityInvRotatedCofiberShortComplexComparisonMap
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

/-- The second component of the inverse-rotated cofiber short-complex
comparison is the source map. -/
theorem stableInfinityInvRotatedCofiberShortComplexComparisonMap_τ₂
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityInvRotatedCofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).τ₂ =
      sourceMap :=
  rfl

/-- The third component of the inverse-rotated cofiber short-complex
comparison is the target map. -/
theorem stableInfinityInvRotatedCofiberShortComplexComparisonMap_τ₃
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticDMgmComparisonSource
      .stableInfinityInvRotatedCofiberShortComplexComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).τ₃ =
      targetMap :=
  rfl

/-- The first square of the rotated cofiber short-complex comparison. -/
theorem stableInfinityRotatedCofiberShortComplexComparisonMap_comm₁₂
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    targetMap ≫
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityRotatedCofiberShortComplex morphism₂).f =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityRotatedCofiberShortComplex morphism₁).f ≫
        TraceAnalyticDMgmComparisonSource
          .stableInfinityCofiberComparisonMap
            morphism₁
            morphism₂
            sourceMap
            targetMap
            square :=
  (TraceAnalyticDMgmComparisonSource
    .stableInfinityRotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₁₂

/-- The second square of the rotated cofiber short-complex comparison. -/
theorem stableInfinityRotatedCofiberShortComplexComparisonMap_comm₂₃
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticDMgmComparisonSource
        .stableInfinityCofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityRotatedCofiberShortComplex morphism₂).g =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityRotatedCofiberShortComplex morphism₁).g ≫
        sourceMap⟦(1 : ℤ)⟧' :=
  (TraceAnalyticDMgmComparisonSource
    .stableInfinityRotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₂₃

/-- The first square of the inverse-rotated cofiber short-complex
comparison. -/
theorem stableInfinityInvRotatedCofiberShortComplexComparisonMap_comm₁₂
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
          .stableInfinityInvRotatedCofiberShortComplex morphism₂).f =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityInvRotatedCofiberShortComplex morphism₁).f ≫
        sourceMap :=
  (TraceAnalyticDMgmComparisonSource
    .stableInfinityInvRotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₁₂

/-- The second square of the inverse-rotated cofiber short-complex
comparison. -/
theorem stableInfinityInvRotatedCofiberShortComplexComparisonMap_comm₂₃
    {source₁ target₁ source₂ target₂ :
      TraceAnalyticDMgmComparisonSource}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (TraceAnalyticDMgmComparisonSource
          .stableInfinityInvRotatedCofiberShortComplex morphism₂).g =
      (TraceAnalyticDMgmComparisonSource
        .stableInfinityInvRotatedCofiberShortComplex morphism₁).g ≫
        targetMap :=
  (TraceAnalyticDMgmComparisonSource
    .stableInfinityInvRotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₂₃

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
