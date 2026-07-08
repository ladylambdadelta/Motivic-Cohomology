import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.YonedaExact.Fiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Owner

/-!
# Global comparison of fiber and inverse-rotated cofiber exactness

This file lifts the package-level agreement between fiber Yoneda exactness and
inverse-rotated cofiber Yoneda exactness into the global stable-category
certificate surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Globally, the covariant and contravariant Yoneda exactness witnesses for
the chosen fiber short complex agree with the inverse-rotated cofiber
short-complex exactness witnesses. -/
theorem
    traceAnalyticStableInfinityCategory_global_fiber_exact_eq_invRotated :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target)
      (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
      (rightProbe : StableInfinityOwner.PresentedCategory),
      traceAnalyticStableInfinityCategory_fiberCoyonedaShortComplex_exact
          morphism leftProbe =
        traceAnalyticStableInfinityCategory_invRotatedCofiberCoyonedaShortComplex_exact
          morphism leftProbe ∧
        traceAnalyticStableInfinityCategory_fiberYonedaShortComplex_exact
            morphism rightProbe =
          traceAnalyticStableInfinityCategory_invRotatedCofiberYonedaShortComplex_exact
            morphism rightProbe :=
  fun morphism leftProbe rightProbe =>
    And.intro
      (traceAnalyticStableInfinityCategory_fiberCoyonedaShortComplex_exact_eq_invRotated
        morphism
        leftProbe)
      (traceAnalyticStableInfinityCategory_fiberYonedaShortComplex_exact_eq_invRotated
        morphism
        rightProbe)

end AnalyticMotives
end LFunctions
end Boundary
