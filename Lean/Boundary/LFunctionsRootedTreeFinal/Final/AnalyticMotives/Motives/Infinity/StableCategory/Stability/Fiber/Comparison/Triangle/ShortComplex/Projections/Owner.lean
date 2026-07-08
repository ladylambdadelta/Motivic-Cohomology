import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Comparison.Triangle.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Comparison.Triangle.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Fiber.Comparison.Projections.Owner

/-!
# Projection compatibility between fiber triangle and short-complex comparisons

This owner file records that projecting the fiber short-complex comparison
agrees with projecting the corresponding fiber triangle comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- First projection compatibility between fiber short-complex and triangle
comparison morphisms. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .fiberComparison_shortComplexFirstProjection_eq_triangleFirstProjection
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (ShortComplex.π₁ :
        ShortComplex StableInfinityOwner.PresentedCategory ⥤
          StableInfinityOwner.PresentedCategory).map
        (TraceAnalyticStableMotiveQuasicategory
          .fiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      TraceAnalyticStableMotiveQuasicategory.triangleFirstProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .fiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

/-- Second projection compatibility between fiber short-complex and triangle
comparison morphisms. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .fiberComparison_shortComplexSecondProjection_eq_triangleSecondProjection
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (ShortComplex.π₂ :
        ShortComplex StableInfinityOwner.PresentedCategory ⥤
          StableInfinityOwner.PresentedCategory).map
        (TraceAnalyticStableMotiveQuasicategory
          .fiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      TraceAnalyticStableMotiveQuasicategory.triangleSecondProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .fiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

/-- Third projection compatibility between fiber short-complex and triangle
comparison morphisms. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .fiberComparison_shortComplexThirdProjection_eq_triangleThirdProjection
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (ShortComplex.π₃ :
        ShortComplex StableInfinityOwner.PresentedCategory ⥤
          StableInfinityOwner.PresentedCategory).map
        (TraceAnalyticStableMotiveQuasicategory
          .fiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      TraceAnalyticStableMotiveQuasicategory.triangleThirdProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .fiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
