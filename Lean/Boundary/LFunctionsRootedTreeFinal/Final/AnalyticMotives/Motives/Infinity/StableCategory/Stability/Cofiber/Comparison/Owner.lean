import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Completion.Owner

/-!
# Cofiber comparison maps in the analytic stable motive category

This owner file extracts the cofiber map induced by a commutative square
between morphisms from the pretriangulated completion theorem applied to the
chosen cofiber triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The induced map between chosen cofibers of two morphisms connected by a
commutative square. -/
def TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.cofiberObject morphism₁ ⟶
      TraceAnalyticStableMotiveQuasicategory.cofiberObject morphism₂ :=
  TraceAnalyticStableMotiveQuasicategory.completedTriangleMap₃
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism₁)
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism₂)
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle_distinguished morphism₁)
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle_distinguished morphism₂)
    sourceMap
    targetMap
    square

/-- The induced cofiber comparison map makes the cocone square commute. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap_cocone
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap morphism₁ ≫
        TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square =
      targetMap ≫
        TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap
          morphism₂ :=
  TraceAnalyticStableMotiveQuasicategory.completedTriangleMap₃_mor₂
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism₁)
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism₂)
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle_distinguished morphism₁)
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle_distinguished morphism₂)
    sourceMap
    targetMap
    square

/-- The induced cofiber comparison map makes the boundary square commute. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap_boundary
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.cofiberBoundary morphism₁ ≫
        sourceMap⟦(1 : ℤ)⟧' =
      TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        TraceAnalyticStableMotiveQuasicategory.cofiberBoundary
          morphism₂ :=
  TraceAnalyticStableMotiveQuasicategory.completedTriangleMap₃_mor₃
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism₁)
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism₂)
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle_distinguished morphism₁)
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle_distinguished morphism₂)
    sourceMap
    targetMap
    square

end AnalyticMotives
end LFunctions
end Boundary
