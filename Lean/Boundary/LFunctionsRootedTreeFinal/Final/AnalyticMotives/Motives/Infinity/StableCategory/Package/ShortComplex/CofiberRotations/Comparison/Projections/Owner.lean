import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.CofiberRotations.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.CofiberRotations.Comparison.Projections.Owner

/-!
# Package-level projections on rotated cofiber short-complex comparisons

This owner file exposes through `traceAnalyticStableInfinityCategory` the
images of rotated and inverse-rotated cofiber short-complex comparison
morphisms under the three short-complex projection functors.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first projection sends the package-level rotated comparison to the
target map. -/
theorem
    traceAnalyticStableInfinityCategory_shortComplexFirstProjection_map_rotatedCofiberShortComplexComparisonMap
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
        (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      targetMap :=
  rfl

/-- The second projection sends the package-level rotated comparison to the
cofiber comparison map. -/
theorem
    traceAnalyticStableInfinityCategory_shortComplexSecondProjection_map_rotatedCofiberShortComplexComparisonMap
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
        (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      traceAnalyticStableInfinityCategory_cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The third projection sends the package-level rotated comparison to the
shifted source map. -/
theorem
    traceAnalyticStableInfinityCategory_shortComplexThirdProjection_map_rotatedCofiberShortComplexComparisonMap
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
        (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      sourceMap⟦(1 : ℤ)⟧' :=
  rfl

/-- The first projection sends the package-level inverse-rotated comparison
to the desuspended cofiber comparison map. -/
theorem
    traceAnalyticStableInfinityCategory_shortComplexFirstProjection_map_invRotatedCofiberShortComplexComparisonMap
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
        (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      (traceAnalyticStableInfinityCategory_cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square)⟦(-1 : ℤ)⟧' :=
  rfl

/-- The second projection sends the package-level inverse-rotated comparison
to the source map. -/
theorem
    traceAnalyticStableInfinityCategory_shortComplexSecondProjection_map_invRotatedCofiberShortComplexComparisonMap
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
        (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      sourceMap :=
  rfl

/-- The third projection sends the package-level inverse-rotated comparison
to the target map. -/
theorem
    traceAnalyticStableInfinityCategory_shortComplexThirdProjection_map_invRotatedCofiberShortComplexComparisonMap
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
        (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplexComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) =
      targetMap :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
