import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.YonedaExact.Fiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.YonedaExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.YonedaExact.Fiber.Comparison.Owner

/-!
# Package-level comparison of fiber and inverse-rotated cofiber exactness

This owner file exposes through `traceAnalyticStableInfinityCategory` that
the fiber Yoneda exactness witnesses agree with the inverse-rotated cofiber
exactness witnesses.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Package-level covariant fiber exactness agrees with the inverse-rotated
cofiber exactness witness. -/
theorem
    traceAnalyticStableInfinityCategory_fiberCoyonedaShortComplex_exact_eq_invRotated
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    traceAnalyticStableInfinityCategory_fiberCoyonedaShortComplex_exact
        morphism probe =
      traceAnalyticStableInfinityCategory_invRotatedCofiberCoyonedaShortComplex_exact
        morphism probe :=
  Subsingleton.elim
    (traceAnalyticStableInfinityCategory_fiberCoyonedaShortComplex_exact
      morphism probe)
    (traceAnalyticStableInfinityCategory_invRotatedCofiberCoyonedaShortComplex_exact
      morphism probe)

/-- Package-level contravariant fiber exactness agrees with the
inverse-rotated cofiber exactness witness. -/
theorem
    traceAnalyticStableInfinityCategory_fiberYonedaShortComplex_exact_eq_invRotated
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory_fiberYonedaShortComplex_exact
        morphism probe =
      traceAnalyticStableInfinityCategory_invRotatedCofiberYonedaShortComplex_exact
        morphism probe :=
  Subsingleton.elim
    (traceAnalyticStableInfinityCategory_fiberYonedaShortComplex_exact
      morphism probe)
    (traceAnalyticStableInfinityCategory_invRotatedCofiberYonedaShortComplex_exact
      morphism probe)

end AnalyticMotives
end LFunctions
end Boundary
