import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Comparison.Owner

/-!
# Projections from the global comparison certificate

This file exposes the global square-comparison certificate fields without
requiring downstream files to unfold the concrete certificate constructor.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The global comparison certificate supplies the cofiber comparison map. -/
def traceAnalyticStableInfinityCategory_global_comparison_cofiberMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberObject morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberObject morphism₂ :=
  (traceAnalyticStableInfinityCategory_global_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).cofiberMap

/-- The global comparison certificate supplies cocone compatibility. -/
theorem traceAnalyticStableInfinityCategory_global_comparison_cocone
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
  (traceAnalyticStableInfinityCategory_global_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).cocone

/-- The global comparison certificate supplies boundary compatibility. -/
theorem traceAnalyticStableInfinityCategory_global_comparison_boundary
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
  (traceAnalyticStableInfinityCategory_global_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).boundary

/-- The global comparison certificate supplies the cofiber-triangle
comparison map. -/
def traceAnalyticStableInfinityCategory_global_comparison_cofiberTriangleMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberTriangle morphism₂ :=
  (traceAnalyticStableInfinityCategory_global_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).cofiberTriangleMap

/-- The global comparison certificate supplies the rotated cofiber-triangle
comparison map. -/
def
    traceAnalyticStableInfinityCategory_global_comparison_rotatedCofiberTriangleMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.rotatedCofiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.rotatedCofiberTriangle morphism₂ :=
  (traceAnalyticStableInfinityCategory_global_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).rotatedCofiberTriangleMap

/-- The global comparison certificate supplies the inverse-rotated
cofiber-triangle comparison map. -/
def
    traceAnalyticStableInfinityCategory_global_comparison_invRotatedCofiberTriangleMap
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
  (traceAnalyticStableInfinityCategory_global_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).invRotatedCofiberTriangleMap

/-- The global comparison certificate supplies the fiber-triangle comparison
map. -/
def traceAnalyticStableInfinityCategory_global_comparison_fiberTriangleMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.fiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.fiberTriangle morphism₂ :=
  (traceAnalyticStableInfinityCategory_global_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).fiberTriangleMap

/-- The global comparison certificate supplies the cofiber-short-complex
comparison map. -/
def
    traceAnalyticStableInfinityCategory_global_comparison_cofiberShortComplexMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.cofiberShortComplex morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberShortComplex morphism₂ :=
  (traceAnalyticStableInfinityCategory_global_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).cofiberShortComplexMap

/-- The global comparison certificate supplies the fiber-short-complex
comparison map. -/
def traceAnalyticStableInfinityCategory_global_comparison_fiberShortComplexMap
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    traceAnalyticStableInfinityCategory.fiberShortComplex morphism₁ ⟶
      traceAnalyticStableInfinityCategory.fiberShortComplex morphism₂ :=
  (traceAnalyticStableInfinityCategory_global_comparison_certificate
    morphism₁
    morphism₂
    sourceMap
    targetMap
    square).fiberShortComplexMap

end AnalyticMotives
end LFunctions
end Boundary
