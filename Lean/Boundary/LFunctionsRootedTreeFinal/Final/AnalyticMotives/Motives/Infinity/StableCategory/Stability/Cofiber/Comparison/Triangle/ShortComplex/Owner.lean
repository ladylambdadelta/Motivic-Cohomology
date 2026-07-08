import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Triangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Cofiber.Comparison.Owner

/-!
# Compatibility of cofiber triangle and short-complex comparisons

This owner file records that the triangle comparison morphism and the
short-complex comparison morphism induced by the same commutative square have
the same three underlying maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first component of the cofiber short-complex comparison is the first
component of the cofiber triangle comparison. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap_τ₁_eq_triangle_hom₁
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
      (TraceAnalyticStableMotiveQuasicategory
        .cofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).hom₁ :=
  rfl

/-- The second component of the cofiber short-complex comparison is the second
component of the cofiber triangle comparison. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap_τ₂_eq_triangle_hom₂
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
      (TraceAnalyticStableMotiveQuasicategory
        .cofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).hom₂ :=
  rfl

/-- The third component of the cofiber short-complex comparison is the third
component of the cofiber triangle comparison. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplexComparisonMap_τ₃_eq_triangle_hom₃
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
      (TraceAnalyticStableMotiveQuasicategory
        .cofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square).hom₃ :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
