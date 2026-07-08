import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Owner

/-!
# Cofiber-comparison morphisms of chosen cofiber triangles

This owner file packages the cofiber comparison map induced by a commutative
square as an actual morphism between the chosen cofiber triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The morphism between chosen cofiber triangles induced by a commutative
square between morphisms. -/
def TraceAnalyticStableMotiveQuasicategory.cofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism₁ ⟶
      TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism₂ :=
  Pretriangulated.Triangle.homMk
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism₁)
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism₂)
    sourceMap
    targetMap
    (TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square)
    square
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberComparisonMap_cocone
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square)
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberComparisonMap_boundary
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square)

/-- The first component of the cofiber triangle comparison is the source map
of the original commutative square. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberTriangleComparisonMap_hom₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₁ =
      sourceMap :=
  rfl

/-- The second component of the cofiber triangle comparison is the target map
of the original commutative square. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberTriangleComparisonMap_hom₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₂ =
      targetMap :=
  rfl

/-- The third component of the cofiber triangle comparison is the chosen
cofiber comparison map. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberTriangleComparisonMap_hom₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₃ =
      TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The first square of the cofiber triangle comparison is the original
commutative square. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberTriangleComparisonMap_comm₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle morphism₁).mor₁ ≫ targetMap =
      sourceMap ≫
        (TraceAnalyticStableMotiveQuasicategory
          .cofiberTriangle morphism₂).mor₁ :=
  (TraceAnalyticStableMotiveQuasicategory
    .cofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁

/-- The second square of the cofiber triangle comparison is the cocone
compatibility square. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberTriangleComparisonMap_comm₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle morphism₁).mor₂ ≫
        TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square =
      targetMap ≫
        (TraceAnalyticStableMotiveQuasicategory
          .cofiberTriangle morphism₂).mor₂ :=
  (TraceAnalyticStableMotiveQuasicategory
    .cofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂

/-- The third square of the cofiber triangle comparison is the boundary
compatibility square. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberTriangleComparisonMap_comm₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle morphism₁).mor₃ ≫ sourceMap⟦(1 : ℤ)⟧' =
      TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        (TraceAnalyticStableMotiveQuasicategory
          .cofiberTriangle morphism₂).mor₃ :=
  (TraceAnalyticStableMotiveQuasicategory
    .cofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₃

end AnalyticMotives
end LFunctions
end Boundary
