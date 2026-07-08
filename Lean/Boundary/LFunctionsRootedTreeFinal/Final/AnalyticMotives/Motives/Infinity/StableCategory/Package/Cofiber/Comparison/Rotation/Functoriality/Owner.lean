import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Rotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Rotation.Functoriality.Owner

/-!
# Package-level functorial origin of rotated cofiber-comparison morphisms

This owner file exposes through `traceAnalyticStableInfinityCategory` that
the rotated and inverse-rotated cofiber comparison morphisms are exactly the
images of the unrotated cofiber triangle comparison morphism under the package
triangle rotation functors.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level rotated cofiber-comparison morphism is the package
rotation functor applied to the cofiber triangle comparison morphism. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap_eq_rotateFunctor_map
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      traceAnalyticStableInfinityCategory.triangleRotateFunctor.map
        (traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

/-- The package-level inverse-rotated cofiber-comparison morphism is the
package inverse-rotation functor applied to the cofiber triangle comparison
morphism. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap_eq_invRotateFunctor_map
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      traceAnalyticStableInfinityCategory.triangleInvRotateFunctor.map
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
