import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Owner

/-!
# Cofiber-comparison morphisms of short complexes

This owner file packages the cofiber comparison map induced by a commutative
square as an actual morphism between the chosen cofiber short complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The morphism between chosen cofiber short complexes induced by a
commutative square between morphisms. -/
def TraceAnalyticStableMotiveQuasicategory.cofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.cofiberShortComplex morphism₁ ⟶
      TraceAnalyticStableMotiveQuasicategory.cofiberShortComplex morphism₂ :=
  ShortComplex.homMk
    sourceMap
    targetMap
    (TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square)
    square.symm
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberComparisonMap_cocone
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).symm

/-- The first component of the cofiber short-complex comparison is the source
map of the original commutative square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap_τ₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₁ =
      sourceMap :=
  rfl

/-- The second component of the cofiber short-complex comparison is the target
map of the original commutative square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap_τ₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₂ =
      targetMap :=
  rfl

/-- The third component of the cofiber short-complex comparison is the chosen
cofiber comparison map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap_τ₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₃ =
      TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The first square of the cofiber short-complex comparison is the original
commutative square, in short-complex orientation. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap_comm₁₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (TraceAnalyticStableMotiveQuasicategory
          .cofiberShortComplex morphism₂).f =
      (TraceAnalyticStableMotiveQuasicategory
        .cofiberShortComplex morphism₁).f ≫
        targetMap :=
  (TraceAnalyticStableMotiveQuasicategory
    .cofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁₂

/-- The second square of the cofiber short-complex comparison is the cocone
compatibility square, in short-complex orientation. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap_comm₂₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    targetMap ≫
        (TraceAnalyticStableMotiveQuasicategory
          .cofiberShortComplex morphism₂).g =
      (TraceAnalyticStableMotiveQuasicategory
        .cofiberShortComplex morphism₁).g ≫
        TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  (TraceAnalyticStableMotiveQuasicategory
    .cofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂₃

end AnalyticMotives
end LFunctions
end Boundary
