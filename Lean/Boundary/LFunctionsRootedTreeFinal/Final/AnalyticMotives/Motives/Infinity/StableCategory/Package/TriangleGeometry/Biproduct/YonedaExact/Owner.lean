import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Biproduct.YonedaExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.TriangleGeometry.Biproduct.ShortComplex.Owner

/-!
# Package-level Yoneda exactness for binary biproduct triangles

This owner file exposes Yoneda exactness for package-level binary biproduct
and binary product short complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Package-level covariant preadditive Yoneda exactness for binary
biproduct short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_binaryBiproductCoyonedaShortComplex_exact
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory_binaryBiproductShortComplex
      left right).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .binaryBiproductCoyonedaShortComplex_exact left right probe

/-- Package-level contravariant preadditive Yoneda exactness for binary
biproduct short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_binaryBiproductYonedaShortComplex_exact
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory_binaryBiproductShortComplex
      left right).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .binaryBiproductYonedaShortComplex_exact left right probe

/-- Package-level covariant preadditive Yoneda exactness for binary product
short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_binaryProductCoyonedaShortComplex_exact
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory_binaryProductShortComplex
      left right).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .binaryProductCoyonedaShortComplex_exact left right probe

/-- Package-level contravariant preadditive Yoneda exactness for binary
product short complexes. -/
theorem
    traceAnalyticStableInfinityCategory_binaryProductYonedaShortComplex_exact
    (left right : StableInfinityOwner.PresentedCategory)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory_binaryProductShortComplex
      left right).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .binaryProductYonedaShortComplex_exact left right probe

end AnalyticMotives
end LFunctions
end Boundary
