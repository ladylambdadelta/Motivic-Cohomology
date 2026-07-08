import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Owner

/-!
# Package-level cofiber comparison maps

This owner file exposes through `traceAnalyticStableInfinityCategory` the map
between chosen cofibers induced by a commutative square between morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level induced map between chosen cofibers of two morphisms
connected by a commutative square. -/
def traceAnalyticStableInfinityCategory_cofiberComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberObject morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberObject morphism₂ :=
  traceAnalyticStableInfinityCategory.cofiberComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The package-level induced cofiber comparison map makes the cocone square
commute. -/
theorem traceAnalyticStableInfinityCategory_cofiberComparisonMap_cocone
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism₁ ≫
        traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square =
      targetMap ≫
        traceAnalyticStableInfinityCategory.cofiberCoconeMap
          morphism₂ :=
  traceAnalyticStableInfinityCategory.cofiberComparisonMap_cocone
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The package-level induced cofiber comparison map makes the boundary square
commute. -/
theorem traceAnalyticStableInfinityCategory_cofiberComparisonMap_boundary
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberBoundary morphism₁ ≫
        sourceMap⟦(1 : ℤ)⟧' =
      traceAnalyticStableInfinityCategory_cofiberComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        traceAnalyticStableInfinityCategory.cofiberBoundary
          morphism₂ :=
  traceAnalyticStableInfinityCategory.cofiberComparisonMap_boundary
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

end AnalyticMotives
end LFunctions
end Boundary
