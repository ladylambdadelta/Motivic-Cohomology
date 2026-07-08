import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Cofiber.Comparison.Triangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Comparison.Rotation.Owner

/-!
# Package-level rotations of cofiber-comparison triangle morphisms

This owner file exposes through `traceAnalyticStableInfinityCategory` the
rotated and inverse-rotated cofiber-comparison triangle morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level rotated cofiber-comparison morphism induced by a
commutative square. -/
def traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.rotatedCofiberTriangle
        morphism₁ ⟶
      traceAnalyticStableInfinityCategory.rotatedCofiberTriangle
        morphism₂ :=
  traceAnalyticStableInfinityCategory
    .rotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The package-level inverse-rotated cofiber-comparison morphism induced by
a commutative square. -/
def traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
        morphism₁ ⟶
      traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
        morphism₂ :=
  traceAnalyticStableInfinityCategory
    .invRotatedCofiberTriangleComparisonMap
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square

/-- The first component of the package-level rotated cofiber-comparison
morphism is the target map of the original commutative square. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap_hom₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₁ =
      targetMap :=
  rfl

/-- The second component of the package-level rotated cofiber-comparison
morphism is the chosen cofiber comparison map. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap_hom₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₂ =
      traceAnalyticStableInfinityCategory_cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square :=
  rfl

/-- The third component of the package-level rotated cofiber-comparison
morphism is the shifted source map. -/
theorem
    traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap_hom₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₃ =
      sourceMap⟦(1 : ℤ)⟧' :=
  rfl

/-- The first component of the package-level inverse-rotated cofiber-comparison
morphism is the shifted cofiber comparison map. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap_hom₁
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₁ =
      (traceAnalyticStableInfinityCategory_cofiberComparisonMap
        morphism₁
        morphism₂
        sourceMap
        targetMap
        square)⟦(-1 : ℤ)⟧' :=
  rfl

/-- The second component of the package-level inverse-rotated cofiber-comparison
morphism is the source map of the original commutative square. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap_hom₂
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square).hom₂ =
      sourceMap :=
  rfl

/-- The third component of the package-level inverse-rotated cofiber-comparison
morphism is the target map of the original commutative square. -/
theorem
    traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap_hom₃
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    (traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMap
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
