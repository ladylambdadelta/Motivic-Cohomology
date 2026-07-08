import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Comparison.Triangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Fiber.Owner

/-!
# Fiber-comparison morphisms of short complexes

This owner file packages the fiber-triangle comparison induced by a
commutative square as an actual morphism between the chosen fiber short
complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The morphism between chosen fiber short complexes induced by a
commutative square between morphisms. -/
def TraceAnalyticStableMotiveQuasicategory.fiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.fiberShortComplex morphism₁ ⟶
      TraceAnalyticStableMotiveQuasicategory.fiberShortComplex morphism₂ :=
  ShortComplex.homMk
    ((TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square)⟦(-1 : ℤ)⟧')
    sourceMap
    targetMap
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₁.symm
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).comm₂.symm

/-- The first component of the fiber short-complex comparison is the
desuspended cofiber comparison map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplexComparisonMap_τ₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₁ =
      (TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square)⟦(-1 : ℤ)⟧' :=
  rfl

/-- The second component of the fiber short-complex comparison is the source
map of the original commutative square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplexComparisonMap_τ₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₂ =
      sourceMap :=
  rfl

/-- The third component of the fiber short-complex comparison is the target
map of the original commutative square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplexComparisonMap_τ₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₃ =
      targetMap :=
  rfl

/-- The first square of the fiber short-complex comparison is the fiber-map
compatibility square, in short-complex orientation. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplexComparisonMap_comm₁₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square)⟦(-1 : ℤ)⟧' ≫
        (TraceAnalyticStableMotiveQuasicategory
          .fiberShortComplex morphism₂).f =
      (TraceAnalyticStableMotiveQuasicategory
        .fiberShortComplex morphism₁).f ≫
        sourceMap :=
  (TraceAnalyticStableMotiveQuasicategory
    .fiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁₂

/-- The second square of the fiber short-complex comparison is the original
commutative square, in short-complex orientation. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplexComparisonMap_comm₂₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (TraceAnalyticStableMotiveQuasicategory
          .fiberShortComplex morphism₂).g =
      (TraceAnalyticStableMotiveQuasicategory
        .fiberShortComplex morphism₁).g ≫
        targetMap :=
  (TraceAnalyticStableMotiveQuasicategory
    .fiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂₃

end AnalyticMotives
end LFunctions
end Boundary
