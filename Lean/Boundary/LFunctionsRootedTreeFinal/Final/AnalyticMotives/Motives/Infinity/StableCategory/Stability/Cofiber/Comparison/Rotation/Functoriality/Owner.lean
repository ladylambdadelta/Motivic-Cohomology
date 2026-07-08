import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Rotation.Owner

/-!
# Functorial origin of rotated cofiber-comparison morphisms

This owner file records that the rotated and inverse-rotated cofiber
comparison morphisms are exactly the images of the unrotated cofiber triangle
comparison morphism under the triangle rotation functors.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The rotated cofiber-comparison morphism is the rotation functor applied to
the cofiber triangle comparison morphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap_eq_rotateFunctor_map
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory
        .rotatedCofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      TraceAnalyticStableMotiveQuasicategory.triangleRotateFunctor.map
        (TraceAnalyticStableMotiveQuasicategory
          .cofiberTriangleComparisonMap
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square) :=
  rfl

/-- The inverse-rotated cofiber-comparison morphism is the inverse-rotation
functor applied to the cofiber triangle comparison morphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangleComparisonMap_eq_invRotateFunctor_map
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberTriangleComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square =
      TraceAnalyticStableMotiveQuasicategory.triangleInvRotateFunctor.map
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
