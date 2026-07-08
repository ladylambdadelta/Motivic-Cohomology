import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.YonedaExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Owner

/-!
# Global rotated cofiber Yoneda exactness

This file bundles the covariant and contravariant Yoneda exactness facts for
rotated and inverse-rotated cofiber short complexes into the global
stable-category certificate surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Globally, rotated and inverse-rotated cofiber short complexes are exact
after covariant and contravariant preadditive Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_rotatedCofiber_yoneda_exact_certificate :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target)
      (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
      (rightProbe : StableInfinityOwner.PresentedCategory),
      ((traceAnalyticStableInfinityCategory
        .rotatedCofiberShortComplex morphism).map
          (preadditiveCoyoneda.obj leftProbe)).Exact ∧
        ((traceAnalyticStableInfinityCategory
          .rotatedCofiberShortComplex morphism).op.map
            (preadditiveYoneda.obj rightProbe)).Exact ∧
          ((traceAnalyticStableInfinityCategory
            .invRotatedCofiberShortComplex morphism).map
              (preadditiveCoyoneda.obj leftProbe)).Exact ∧
            ((traceAnalyticStableInfinityCategory
              .invRotatedCofiberShortComplex morphism).op.map
                (preadditiveYoneda.obj rightProbe)).Exact :=
  fun morphism leftProbe rightProbe =>
    And.intro
      (traceAnalyticStableInfinityCategory_rotatedCofiberCoyonedaShortComplex_exact
        morphism
        leftProbe)
      (And.intro
        (traceAnalyticStableInfinityCategory_rotatedCofiberYonedaShortComplex_exact
          morphism
          rightProbe)
        (And.intro
          (traceAnalyticStableInfinityCategory_invRotatedCofiberCoyonedaShortComplex_exact
            morphism
            leftProbe)
          (traceAnalyticStableInfinityCategory_invRotatedCofiberYonedaShortComplex_exact
            morphism
            rightProbe)))

end AnalyticMotives
end LFunctions
end Boundary
