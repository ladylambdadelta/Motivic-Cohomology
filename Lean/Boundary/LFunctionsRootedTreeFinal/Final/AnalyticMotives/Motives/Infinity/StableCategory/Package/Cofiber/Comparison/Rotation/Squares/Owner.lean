import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Rotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Rotation.Squares.Owner

/-!
# Package-level triangle-square laws for rotated cofiber comparisons

This owner file exposes through `traceAnalyticStableInfinityCategory` the
three triangle-morphism commutative squares for the rotated and inverse-rotated
cofiber-comparison morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first square of the package-level rotated cofiber-comparison
morphism. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap_comm₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory
      .rotatedCofiberTriangle morphism₁).mor₁ ≫
        traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square =
      targetMap ≫
        (traceAnalyticStableInfinityCategory
          .rotatedCofiberTriangle morphism₂).mor₁ :=
  (traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁

/-- The second square of the package-level rotated cofiber-comparison
morphism. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap_comm₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory
      .rotatedCofiberTriangle morphism₁).mor₂ ≫
        sourceMap⟦(1 : ℤ)⟧' =
      traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        (traceAnalyticStableInfinityCategory
          .rotatedCofiberTriangle morphism₂).mor₂ :=
  (traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂

/-- The third square of the package-level rotated cofiber-comparison
morphism. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap_comm₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory
      .rotatedCofiberTriangle morphism₁).mor₃ ≫ targetMap⟦(1 : ℤ)⟧' =
      sourceMap⟦(1 : ℤ)⟧' ≫
        (traceAnalyticStableInfinityCategory
          .rotatedCofiberTriangle morphism₂).mor₃ :=
  (traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₃

/-- The first square of the package-level inverse-rotated cofiber-comparison
morphism. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap_comm₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory
      .invRotatedCofiberTriangle morphism₁).mor₁ ≫ sourceMap =
      (traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square)⟦(-1 : ℤ)⟧' ≫
        (traceAnalyticStableInfinityCategory
          .invRotatedCofiberTriangle morphism₂).mor₁ :=
  (traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁

/-- The second square of the package-level inverse-rotated cofiber-comparison
morphism. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap_comm₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory
      .invRotatedCofiberTriangle morphism₁).mor₂ ≫ targetMap =
      sourceMap ≫
        (traceAnalyticStableInfinityCategory
          .invRotatedCofiberTriangle morphism₂).mor₂ :=
  (traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂

/-- The third square of the package-level inverse-rotated cofiber-comparison
morphism. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap_comm₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory
      .invRotatedCofiberTriangle morphism₁).mor₃ ≫
        ((traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square)⟦(-1 : ℤ)⟧')⟦(1 : ℤ)⟧' =
      targetMap ≫
        (traceAnalyticStableInfinityCategory
          .invRotatedCofiberTriangle morphism₂).mor₃ :=
  (traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₃

end AnalyticMotives
end LFunctions
end Boundary
