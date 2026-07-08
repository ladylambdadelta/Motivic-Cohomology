import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Biproduct.YonedaExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Finite biproduct stability for analytic stable motives

This owner file records the finite additive geometry used by the stable
infinity category package: binary biproduct and binary product triangles are
distinguished, canonically agree as triangles, and their attached short
complexes are exact after both preadditive Yoneda embeddings.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Binary biproduct triangles are distinguished in the owner-level stable
infinity category of analytic motives. -/
theorem traceAnalyticStableInfinityCategory_binaryBiproductTriangle_mem
    (left right : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory
        .binaryBiproductTriangle left right ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .binaryBiproductTriangle_distinguished left right

/-- Binary product triangles are distinguished in the owner-level stable
infinity category of analytic motives. -/
theorem traceAnalyticStableInfinityCategory_binaryProductTriangle_mem
    (left right : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory
        .binaryProductTriangle left right ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .binaryProductTriangle_distinguished left right

/-- The binary product triangle and binary biproduct triangle agree up to the
canonical triangle isomorphism in the owner-level stable infinity category. -/
def
    traceAnalyticStableInfinityCategory_binaryProductTriangleIsoBinaryBiproductTriangle_owner
    (left right : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.binaryProductTriangle left right ≅
      traceAnalyticStableInfinityCategory.binaryBiproductTriangle
        left right :=
  traceAnalyticStableInfinityCategory
    .binaryProductTriangleIsoBinaryBiproductTriangle left right

/-- Covariant preadditive Yoneda exactness for owner-level binary biproduct
short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_binaryBiproductCoyoneda_exact_owner
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory
      .binaryBiproductShortComplex left right).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .binaryBiproductCoyonedaShortComplex_exact left right probe

/-- Contravariant preadditive Yoneda exactness for owner-level binary
biproduct short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_binaryBiproductYoneda_exact_owner
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .binaryBiproductShortComplex left right).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .binaryBiproductYonedaShortComplex_exact left right probe

/-- Covariant preadditive Yoneda exactness for owner-level binary product
short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_binaryProductCoyoneda_exact_owner
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory
      .binaryProductShortComplex left right).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .binaryProductCoyonedaShortComplex_exact left right probe

/-- Contravariant preadditive Yoneda exactness for owner-level binary product
short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_binaryProductYoneda_exact_owner
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .binaryProductShortComplex left right).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .binaryProductYonedaShortComplex_exact left right probe

end AnalyticMotives
end LFunctions
end Boundary
