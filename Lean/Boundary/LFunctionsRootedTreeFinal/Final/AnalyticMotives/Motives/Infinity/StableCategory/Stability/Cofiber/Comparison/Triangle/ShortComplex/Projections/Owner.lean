import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Triangle.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Triangle.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Cofiber.Comparison.Projections.Owner

/-!
# Projection compatibility between cofiber triangle and short-complex comparisons

This owner file records that projecting the cofiber short-complex comparison
agrees with projecting the corresponding cofiber triangle comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- First projection compatibility between cofiber short-complex and triangle
comparison morphisms. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberComparison_shortComplexFirstProjection_eq_triangleFirstProjection
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
          .cofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      TraceAnalyticStableMotiveQuasicategory.triangleFirstProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .cofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

/-- Second projection compatibility between cofiber short-complex and triangle
comparison morphisms. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberComparison_shortComplexSecondProjection_eq_triangleSecondProjection
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
          .cofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      TraceAnalyticStableMotiveQuasicategory.triangleSecondProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .cofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

/-- Third projection compatibility between cofiber short-complex and triangle
comparison morphisms. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .cofiberComparison_shortComplexThirdProjection_eq_triangleThirdProjection
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
          .cofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      TraceAnalyticStableMotiveQuasicategory.triangleThirdProjection.map
        (TraceAnalyticStableMotiveQuasicategory
          .cofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
