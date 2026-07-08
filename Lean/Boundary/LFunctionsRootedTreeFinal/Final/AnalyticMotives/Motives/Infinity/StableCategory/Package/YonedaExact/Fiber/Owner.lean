import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Fiber.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.YonedaExact.Fiber.Owner

/-!
# Package-level Yoneda exactness for fiber short complexes

This owner file exposes Yoneda exactness for chosen fiber short complexes
through the assembled `traceAnalyticStableInfinityCategory` package.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The assembled stable-infinity package inherits covariant preadditive
Yoneda exactness for chosen fiber short complexes. -/
theorem traceAnalyticStableInfinityCategory_fiberCoyonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((traceAnalyticStableInfinityCategory_fiberShortComplex
      morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .fiberCoyonedaShortComplex_exact morphism probe

/-- The assembled stable-infinity package inherits contravariant preadditive
Yoneda exactness for chosen fiber short complexes. -/
theorem traceAnalyticStableInfinityCategory_fiberYonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory_fiberShortComplex
      morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  traceAnalyticStableInfinityCategory
    .fiberYonedaShortComplex_exact morphism probe

end AnalyticMotives
end LFunctions
end Boundary
