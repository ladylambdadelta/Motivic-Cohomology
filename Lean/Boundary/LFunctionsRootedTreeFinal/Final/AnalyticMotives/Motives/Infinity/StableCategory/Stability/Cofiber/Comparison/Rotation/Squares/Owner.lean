import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Rotation.Owner

/-!
# Triangle-square laws for rotated cofiber-comparison morphisms

This owner file exposes the three triangle-morphism commutative squares for
the rotated and inverse-rotated cofiber-comparison morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first square of the rotated cofiber-comparison morphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap_comm₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangle morphism₁).mor₁ ≫
        TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square =
      targetMap ≫
        (TraceAnalyticStableMotiveQuasicategory
          .rotatedCofiberTriangle morphism₂).mor₁ :=
  (TraceAnalyticStableMotiveQuasicategory
    .rotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁

/-- The second square of the rotated cofiber-comparison morphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap_comm₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangle morphism₁).mor₂ ≫
        sourceMap⟦(1 : ℤ)⟧' =
      TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        (TraceAnalyticStableMotiveQuasicategory
          .rotatedCofiberTriangle morphism₂).mor₂ :=
  (TraceAnalyticStableMotiveQuasicategory
    .rotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂

/-- The third square of the rotated cofiber-comparison morphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap_comm₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangle morphism₁).mor₃ ≫ targetMap⟦(1 : ℤ)⟧' =
      sourceMap⟦(1 : ℤ)⟧' ≫
        (TraceAnalyticStableMotiveQuasicategory
          .rotatedCofiberTriangle morphism₂).mor₃ :=
  (TraceAnalyticStableMotiveQuasicategory
    .rotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₃

/-- The first square of the inverse-rotated cofiber-comparison morphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangleComparisonMap_comm₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangle morphism₁).mor₁ ≫ sourceMap =
      (TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square)⟦(-1 : ℤ)⟧' ≫
        (TraceAnalyticStableMotiveQuasicategory
          .invRotatedCofiberTriangle morphism₂).mor₁ :=
  (TraceAnalyticStableMotiveQuasicategory
    .invRotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁

/-- The second square of the inverse-rotated cofiber-comparison morphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangleComparisonMap_comm₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangle morphism₁).mor₂ ≫ targetMap =
      sourceMap ≫
        (TraceAnalyticStableMotiveQuasicategory
          .invRotatedCofiberTriangle morphism₂).mor₂ :=
  (TraceAnalyticStableMotiveQuasicategory
    .invRotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂

/-- The third square of the inverse-rotated cofiber-comparison morphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangleComparisonMap_comm₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangle morphism₁).mor₃ ≫
        ((TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square)⟦(-1 : ℤ)⟧')⟦(1 : ℤ)⟧' =
      targetMap ≫
        (TraceAnalyticStableMotiveQuasicategory
          .invRotatedCofiberTriangle morphism₂).mor₃ :=
  (TraceAnalyticStableMotiveQuasicategory
    .invRotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₃

end AnalyticMotives
end LFunctions
end Boundary
