import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Comparison.Owner

/-!
# Projections from the comparison certificate

This file exposes named projections from the comparison certificate for a
commutative square in the concrete analytic stable category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The cofiber comparison map carried by the comparison certificate. -/
def traceAnalyticStableInfinityCategory_comparison_cofiberMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberObject morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberObject morphism₂ :=
  (traceAnalyticStableInfinityCategory_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).cofiberMap

/-- The cocone compatibility carried by the comparison certificate. -/
theorem traceAnalyticStableInfinityCategory_comparison_cocone
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism₁ ≫
        traceAnalyticStableInfinityCategory_cofiberComparisonMapFor
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square =
      targetMap ≫
        traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism₂ :=
  (traceAnalyticStableInfinityCategory_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).cocone

/-- The boundary compatibility carried by the comparison certificate. -/
theorem traceAnalyticStableInfinityCategory_comparison_boundary
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberBoundary morphism₁ ≫
        sourceMap⟦(1 : ℤ)⟧' =
      traceAnalyticStableInfinityCategory_cofiberComparisonMapFor
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        traceAnalyticStableInfinityCategory.cofiberBoundary morphism₂ :=
  (traceAnalyticStableInfinityCategory_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).boundary

/-- The cofiber-triangle comparison map carried by the comparison
certificate. -/
def traceAnalyticStableInfinityCategory_comparison_cofiberTriangleMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberTriangle morphism₂ :=
  (traceAnalyticStableInfinityCategory_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).cofiberTriangleMap

/-- The rotated cofiber-triangle comparison map carried by the comparison
certificate. -/
def
    traceAnalyticStableInfinityCategory_comparison_rotatedCofiberTriangleMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.rotatedCofiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.rotatedCofiberTriangle morphism₂ :=
  (traceAnalyticStableInfinityCategory_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).rotatedCofiberTriangleMap

/-- The inverse-rotated cofiber-triangle comparison map carried by the
comparison certificate. -/
def
    traceAnalyticStableInfinityCategory_comparison_invRotatedCofiberTriangleMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
        morphism₂ :=
  (traceAnalyticStableInfinityCategory_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).invRotatedCofiberTriangleMap

/-- The fiber-triangle comparison map carried by the comparison certificate. -/
def traceAnalyticStableInfinityCategory_comparison_fiberTriangleMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.fiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.fiberTriangle morphism₂ :=
  (traceAnalyticStableInfinityCategory_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).fiberTriangleMap

/-- The cofiber-short-complex comparison map carried by the comparison
certificate. -/
def traceAnalyticStableInfinityCategory_comparison_cofiberShortComplexMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberShortComplex morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberShortComplex morphism₂ :=
  (traceAnalyticStableInfinityCategory_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).cofiberShortComplexMap

/-- The fiber-short-complex comparison map carried by the comparison
certificate. -/
def traceAnalyticStableInfinityCategory_comparison_fiberShortComplexMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.fiberShortComplex morphism₁ ⟶
      traceAnalyticStableInfinityCategory.fiberShortComplex morphism₂ :=
  (traceAnalyticStableInfinityCategory_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).fiberShortComplexMap

end AnalyticMotives
end LFunctions
end Boundary
