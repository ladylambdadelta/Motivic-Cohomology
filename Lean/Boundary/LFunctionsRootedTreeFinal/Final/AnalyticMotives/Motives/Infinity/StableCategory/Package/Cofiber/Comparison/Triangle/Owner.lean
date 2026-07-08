import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Triangle.Owner

/-!
# Package-level cofiber-comparison morphisms of chosen cofiber triangles

This owner file exposes through `traceAnalyticStableInfinityCategory` the
triangle morphism induced by a commutative square between morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level morphism between chosen cofiber triangles induced by a
commutative square between morphisms. -/
def traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberTriangle morphism₂ :=
  traceAnalyticStableInfinityCategory.cofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The first component of the package-level cofiber triangle comparison is
the source map of the original commutative square. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap_hom₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₁ =
      sourceMap :=
  rfl

/-- The second component of the package-level cofiber triangle comparison is
the target map of the original commutative square. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap_hom₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₂ =
      targetMap :=
  rfl

/-- The third component of the package-level cofiber triangle comparison is
the chosen package-level cofiber comparison map. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap_hom₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₃ =
      traceAnalyticStableInfinityCategory_cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The first square of the package-level cofiber triangle comparison is the
original commutative square. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap_comm₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory
      .cofiberTriangle morphism₁).mor₁ ≫ targetMap =
      sourceMap ≫
        (traceAnalyticStableInfinityCategory
          .cofiberTriangle morphism₂).mor₁ :=
  (traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₁

/-- The second square of the package-level cofiber triangle comparison is the
cocone compatibility square. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap_comm₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory
      .cofiberTriangle morphism₁).mor₂ ≫
        traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square =
      targetMap ≫
        (traceAnalyticStableInfinityCategory
          .cofiberTriangle morphism₂).mor₂ :=
  (traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₂

/-- The third square of the package-level cofiber triangle comparison is the
boundary compatibility square. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap_comm₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory
      .cofiberTriangle morphism₁).mor₃ ≫ sourceMap⟦(1 : ℤ)⟧' =
      traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        (traceAnalyticStableInfinityCategory
          .cofiberTriangle morphism₂).mor₃ :=
  (traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).comm₃

end AnalyticMotives
end LFunctions
end Boundary
