import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Rotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Comparison.Owner

/-!
# Fiber-triangle comparison morphisms

This owner file names the fiber-side functoriality supplied by stability.  A
commutative square of morphisms induces a morphism between the corresponding
chosen fiber triangles by inverse-rotating the cofiber comparison morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The morphism between chosen fiber triangles induced by a commutative
square. -/
def TraceAnalyticStableMotiveQuasicategory.fiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.fiberTriangle morphism₁ ⟶
      TraceAnalyticStableMotiveQuasicategory.fiberTriangle morphism₂ :=
  TraceAnalyticStableMotiveQuasicategory
    .invRotatedCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square

/-- The fiber-triangle comparison is the inverse-rotated cofiber-triangle
comparison. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .fiberTriangleComparisonMap_eq_invRotatedCofiber
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory
        .fiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square :=
  rfl

/-- The first component of the fiber-triangle comparison is the desuspended
cofiber comparison map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .fiberTriangleComparisonMap_hom₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₁ =
      (TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square)⟦(-1 : ℤ)⟧' :=
  rfl

/-- The second component of the fiber-triangle comparison is the source map
of the original commutative square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .fiberTriangleComparisonMap_hom₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₂ =
      sourceMap :=
  rfl

/-- The third component of the fiber-triangle comparison is the target map of
the original commutative square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .fiberTriangleComparisonMap_hom₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₃ =
      targetMap :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
