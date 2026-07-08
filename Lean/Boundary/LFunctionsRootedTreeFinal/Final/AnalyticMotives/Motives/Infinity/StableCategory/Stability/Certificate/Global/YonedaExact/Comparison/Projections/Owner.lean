import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.YonedaExact.Comparison.Owner

/-!
# Projections from the global fiber exactness comparison

This file exposes the two projections from the global agreement between fiber
Yoneda exactness and inverse-rotated cofiber Yoneda exactness.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The covariant fiber exactness witness agrees with the inverse-rotated
cofiber exactness witness. -/
theorem
    traceAnalyticStableInfinityCategory_global_fiber_coyoneda_exact_eq_invRotated
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory_fiberCoyonedaShortComplex_exact
        morphism probe =
      traceAnalyticStableInfinityCategory_invRotatedCofiberCoyonedaShortComplex_exact
        morphism probe :=
  (traceAnalyticStableInfinityCategory_global_fiber_exact_eq_invRotated
    morphism
    probe
    rightProbe).left

/-- The contravariant fiber exactness witness agrees with the inverse-rotated
cofiber exactness witness. -/
theorem
    traceAnalyticStableInfinityCategory_global_fiber_yoneda_exact_eq_invRotated
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (probe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory_fiberYonedaShortComplex_exact
        morphism probe =
      traceAnalyticStableInfinityCategory_invRotatedCofiberYonedaShortComplex_exact
        morphism probe :=
  (traceAnalyticStableInfinityCategory_global_fiber_exact_eq_invRotated
    morphism
    leftProbe
    probe).right

end AnalyticMotives
end LFunctions
end Boundary
