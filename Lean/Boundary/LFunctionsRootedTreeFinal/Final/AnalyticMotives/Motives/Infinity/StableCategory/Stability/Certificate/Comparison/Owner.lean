import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Owner

/-!
# Comparison certificate for analytic stable motives

This file bundles the functorial comparison behavior of the chosen cofiber,
rotated cofiber, inverse-rotated cofiber, fiber, and short-complex
constructions attached to a commutative square in the concrete analytic stable
category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Concrete comparison data induced by a commutative square in the analytic
stable category.  The fields are the actual comparison morphisms and their
cofiber cocone/boundary compatibilities. -/
structure TraceAnalyticStableInfinityCategoryComparisonCertificate
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) where
  cofiberMap :
    traceAnalyticStableInfinityCategory.cofiberObject morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberObject morphism₂
  cocone :
    traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism₁ ≫
        traceAnalyticStableInfinityCategory_cofiberComparisonMapFor
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square =
      targetMap ≫
        traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism₂
  boundary :
    traceAnalyticStableInfinityCategory.cofiberBoundary morphism₁ ≫
        sourceMap⟦(1 : ℤ)⟧' =
      traceAnalyticStableInfinityCategory_cofiberComparisonMapFor
          morphism₁
          morphism₂
          sourceMap
          targetMap
          square ≫
        traceAnalyticStableInfinityCategory.cofiberBoundary morphism₂
  cofiberTriangleMap :
    traceAnalyticStableInfinityCategory.cofiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberTriangle morphism₂
  rotatedCofiberTriangleMap :
    traceAnalyticStableInfinityCategory.rotatedCofiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.rotatedCofiberTriangle morphism₂
  invRotatedCofiberTriangleMap :
    traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
        morphism₁ ⟶
      traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
        morphism₂
  fiberTriangleMap :
    traceAnalyticStableInfinityCategory.fiberTriangle morphism₁ ⟶
      traceAnalyticStableInfinityCategory.fiberTriangle morphism₂
  cofiberShortComplexMap :
    traceAnalyticStableInfinityCategory.cofiberShortComplex morphism₁ ⟶
      traceAnalyticStableInfinityCategory.cofiberShortComplex morphism₂
  fiberShortComplexMap :
    traceAnalyticStableInfinityCategory.fiberShortComplex morphism₁ ⟶
      traceAnalyticStableInfinityCategory.fiberShortComplex morphism₂

/-- A commutative square in the analytic stable category induces the full
comparison package on chosen cofibers, rotations, fibers, and short complexes,
with the cofiber comparison map compatible with cocone and boundary maps. -/
def traceAnalyticStableInfinityCategory_comparison_certificate
    {source₁ target₁ source₂ target₂ :
      StableInfinityOwner.PresentedCategory}
    (morphism₁ : source₁ ⟶ target₁)
    (morphism₂ : source₂ ⟶ target₂)
    (sourceMap : source₁ ⟶ source₂)
    (targetMap : target₁ ⟶ target₂)
    (square : morphism₁ ≫ targetMap = sourceMap ≫ morphism₂) :
    TraceAnalyticStableInfinityCategoryComparisonCertificate
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square where
  cofiberMap :=
    traceAnalyticStableInfinityCategory_cofiberComparisonMapFor
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square
  cocone :=
    traceAnalyticStableInfinityCategory_cofiberComparisonMapFor_cocone
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square
  boundary :=
    traceAnalyticStableInfinityCategory_cofiberComparisonMapFor_boundary
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square
  cofiberTriangleMap :=
    traceAnalyticStableInfinityCategory_cofiberTriangleComparisonMapFor
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square
  rotatedCofiberTriangleMap :=
    traceAnalyticStableInfinityCategory_rotatedCofiberTriangleComparisonMapFor
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square
  invRotatedCofiberTriangleMap :=
    traceAnalyticStableInfinityCategory_invRotatedCofiberTriangleComparisonMapFor
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square
  fiberTriangleMap :=
    traceAnalyticStableInfinityCategory_fiberTriangleComparisonMapFor
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square
  cofiberShortComplexMap :=
    traceAnalyticStableInfinityCategory_cofiberShortComplexComparisonMapFor
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square
  fiberShortComplexMap :=
    traceAnalyticStableInfinityCategory_fiberShortComplexComparisonMapFor
      morphism₁
      morphism₂
      sourceMap
      targetMap
      square

end AnalyticMotives
end LFunctions
end Boundary
