import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Triangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.InvRotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Rotation.Owner

/-!
# Rotations of cofiber-comparison triangle morphisms

This owner file transports cofiber-comparison triangle morphisms through the
triangle rotation and inverse-rotation functors.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The rotated cofiber-comparison morphism induced by a commutative square. -/
def TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle
        morphism₁ ⟶
      TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle
        morphism₂ :=
  TraceAnalyticStableMotiveQuasicategory.triangleRotateFunctor.map
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square)

/-- The inverse-rotated cofiber-comparison morphism induced by a commutative
square. -/
def TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle
        morphism₁ ⟶
      TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle
        morphism₂ :=
  TraceAnalyticStableMotiveQuasicategory.triangleInvRotateFunctor.map
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square)

/-- The first component of the rotated cofiber-comparison morphism is the
target map of the original commutative square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap_hom₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₁ =
      targetMap :=
  rfl

/-- The second component of the rotated cofiber-comparison morphism is the
chosen cofiber comparison map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap_hom₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₂ =
      TraceAnalyticStableMotiveQuasicategory.cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The third component of the rotated cofiber-comparison morphism is the
shifted source map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap_hom₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₃ =
      sourceMap⟦(1 : ℤ)⟧' :=
  rfl

/-- The first component of the inverse-rotated cofiber-comparison morphism is
the shifted cofiber comparison map. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangleComparisonMap_hom₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangleComparisonMap
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

/-- The second component of the inverse-rotated cofiber-comparison morphism is
the source map of the original commutative square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangleComparisonMap_hom₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₂ =
      sourceMap :=
  rfl

/-- The third component of the inverse-rotated cofiber-comparison morphism is
the target map of the original commutative square. -/
theorem
    TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangleComparisonMap_hom₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangleComparisonMap
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
