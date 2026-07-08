import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Rotation.Squares.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.CofiberRotations.Owner

/-!
# Comparison morphisms for rotated cofiber short complexes

This owner file packages the rotated and inverse-rotated cofiber comparison
morphisms as actual morphisms between the corresponding rotated cofiber short
complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The morphism between rotated cofiber short complexes induced by a
commutative square. -/
def TraceAnalyticStableMotiveQuasicategory.rotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.rotatedCofiberShortComplex
        morphism₁ ⟶
      TraceAnalyticStableMotiveQuasicategory.rotatedCofiberShortComplex
        morphism₂ :=
  ShortComplex.homMk
    targetMap
    (TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square)
    sourceMap⟦(1 : ℤ)⟧'
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap_comm₁
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).symm
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap_comm₂
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).symm

/-- The morphism between inverse-rotated cofiber short complexes induced by a
commutative square. -/
def
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplexComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberShortComplex
        morphism₁ ⟶
      TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberShortComplex
        morphism₂ :=
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
      .invRotatedCofiberTriangleComparisonMap_comm₁
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).symm
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangleComparisonMap_comm₂
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).symm

/-- The first component of the rotated cofiber short-complex comparison is
the target map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplexComparisonMap_τ₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₁ =
      targetMap :=
  rfl

/-- The second component of the rotated cofiber short-complex comparison is
the induced cofiber comparison map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplexComparisonMap_τ₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₂ =
      TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The third component of the rotated cofiber short-complex comparison is
the shifted source map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplexComparisonMap_τ₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₃ =
      sourceMap⟦(1 : ℤ)⟧' :=
  rfl

/-- The first component of the inverse-rotated cofiber short-complex
comparison is the shifted cofiber comparison map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplexComparisonMap_τ₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplexComparisonMap
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

/-- The second component of the inverse-rotated cofiber short-complex
comparison is the source map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplexComparisonMap_τ₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₂ =
      sourceMap :=
  rfl

/-- The third component of the inverse-rotated cofiber short-complex
comparison is the target map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplexComparisonMap_τ₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplexComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).τ₃ =
      targetMap :=
  rfl

/-- The first square of the rotated cofiber short-complex comparison. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplexComparisonMap_comm₁₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    targetMap ≫
        (TraceAnalyticStableMotiveQuasicategory
          .rotatedCofiberShortComplex morphism₂).f =
      (TraceAnalyticStableMotiveQuasicategory
        .rotatedCofiberShortComplex morphism₁).f ≫
        TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  (TraceAnalyticStableMotiveQuasicategory
    .rotatedCofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁₂

/-- The second square of the rotated cofiber short-complex comparison. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplexComparisonMap_comm₂₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        (TraceAnalyticStableMotiveQuasicategory
          .rotatedCofiberShortComplex morphism₂).g =
      (TraceAnalyticStableMotiveQuasicategory
        .rotatedCofiberShortComplex morphism₁).g ≫
        sourceMap⟦(1 : ℤ)⟧' :=
  (TraceAnalyticStableMotiveQuasicategory
    .rotatedCofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂₃

/-- The first square of the inverse-rotated cofiber short-complex comparison. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplexComparisonMap_comm₁₂
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
          .invRotatedCofiberShortComplex morphism₂).f =
      (TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberShortComplex morphism₁).f ≫
        sourceMap :=
  (TraceAnalyticStableMotiveQuasicategory
    .invRotatedCofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁₂

/-- The second square of the inverse-rotated cofiber short-complex
comparison. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplexComparisonMap_comm₂₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    sourceMap ≫
        (TraceAnalyticStableMotiveQuasicategory
          .invRotatedCofiberShortComplex morphism₂).g =
      (TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberShortComplex morphism₁).g ≫
        targetMap :=
  (TraceAnalyticStableMotiveQuasicategory
    .invRotatedCofiberShortComplexComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂₃

end AnalyticMotives
end LFunctions
end Boundary
