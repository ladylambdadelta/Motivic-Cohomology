import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.YonedaExact.Rotations.Owner

/-!
# Global per-morphism Yoneda exactness

This file bundles the covariant and contravariant Yoneda exactness facts for
the chosen cofiber, fiber, rotated cofiber, and inverse-rotated cofiber short
complexes attached to one morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- For every morphism, all four canonical short complexes attached to its
stable fiber/cofiber calculus are exact after covariant and contravariant
preadditive Yoneda evaluation. -/
theorem traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target)
      (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
      (rightProbe : StableInfinityOwner.PresentedCategory),
      ((traceAnalyticStableInfinityCategory
        .cofiberShortComplex morphism).map
          (preadditiveCoyoneda.obj leftProbe)).Exact ∧
        ((traceAnalyticStableInfinityCategory
          .cofiberShortComplex morphism).op.map
            (preadditiveYoneda.obj rightProbe)).Exact ∧
          ((traceAnalyticStableInfinityCategory
            .fiberShortComplex morphism).map
              (preadditiveCoyoneda.obj leftProbe)).Exact ∧
            ((traceAnalyticStableInfinityCategory
              .fiberShortComplex morphism).op.map
                (preadditiveYoneda.obj rightProbe)).Exact ∧
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
      (traceAnalyticStableInfinityCategory_cofiber_coyoneda_exact
        morphism
        leftProbe)
      (And.intro
        (traceAnalyticStableInfinityCategory_cofiber_yoneda_exact
          morphism
          rightProbe)
        (And.intro
          (traceAnalyticStableInfinityCategory_fiber_coyoneda_exact
            morphism
            leftProbe)
          (And.intro
            (traceAnalyticStableInfinityCategory_fiber_yoneda_exact
              morphism
              rightProbe)
            (traceAnalyticStableInfinityCategory_global_rotatedCofiber_yoneda_exact_certificate
              morphism
              leftProbe
              rightProbe))))

end AnalyticMotives
end LFunctions
end Boundary
