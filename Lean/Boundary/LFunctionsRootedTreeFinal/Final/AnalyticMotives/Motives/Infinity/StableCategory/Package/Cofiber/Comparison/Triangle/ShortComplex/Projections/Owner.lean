import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Triangle.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Triangle.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Cofiber.Comparison.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Triangle.ShortComplex.Projections.Owner

/-!
# Package-level projection compatibility for cofiber comparisons

This owner file exposes through `traceAnalyticStableInfinityCategory` that
projecting the cofiber short-complex comparison agrees with projecting the
corresponding cofiber triangle comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Package-level first projection compatibility between cofiber
short-complex and triangle comparison morphisms. -/
theorem
    traceAnalyticStableInfinityCategory_cofiberComparison_shortComplexFirstProjection_eq_triangleFirstProjection
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
        (traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      traceAnalyticStableInfinityCategory.triangleFirstProjection.map
        (traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

/-- Package-level second projection compatibility between cofiber
short-complex and triangle comparison morphisms. -/
theorem
    traceAnalyticStableInfinityCategory_cofiberComparison_shortComplexSecondProjection_eq_triangleSecondProjection
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
        (traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      traceAnalyticStableInfinityCategory.triangleSecondProjection.map
        (traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

/-- Package-level third projection compatibility between cofiber
short-complex and triangle comparison morphisms. -/
theorem
    traceAnalyticStableInfinityCategory_cofiberComparison_shortComplexThirdProjection_eq_triangleThirdProjection
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
        (traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      traceAnalyticStableInfinityCategory.triangleThirdProjection.map
        (traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
