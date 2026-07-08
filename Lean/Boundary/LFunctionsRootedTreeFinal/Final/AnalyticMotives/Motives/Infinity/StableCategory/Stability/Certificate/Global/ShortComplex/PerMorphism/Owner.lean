import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Cofiber.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Fiber.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.CofiberRotations.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Owner

/-!
# Global per-morphism short-complex shape

This file bundles the map identifications for the four canonical short
complexes attached to one morphism in the analytic stable category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- For every morphism, the cofiber, fiber, rotated cofiber, and
inverse-rotated cofiber short complexes have their canonical first and second
maps. -/
theorem traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      (traceAnalyticStableInfinityCategory.cofiberShortComplex morphism).f =
          morphism ∧
        (traceAnalyticStableInfinityCategory.cofiberShortComplex morphism).g =
          traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism ∧
          (traceAnalyticStableInfinityCategory_fiberShortComplex
            morphism).f =
            traceAnalyticStableInfinityCategory.fiberMap morphism ∧
            (traceAnalyticStableInfinityCategory_fiberShortComplex
              morphism).g =
              morphism ∧
              (traceAnalyticStableInfinityCategory.rotatedCofiberShortComplex
                morphism).f =
                traceAnalyticStableInfinityCategory.cofiberCoconeMap
                  morphism ∧
                (traceAnalyticStableInfinityCategory.rotatedCofiberShortComplex
                  morphism).g =
                  traceAnalyticStableInfinityCategory.cofiberBoundary
                    morphism ∧
                  (traceAnalyticStableInfinityCategory
                    .invRotatedCofiberShortComplex morphism).f =
                    -((traceAnalyticStableInfinityCategory.cofiberBoundary
                      morphism)⟦(-1 : ℤ)⟧') ≫
                      (shiftEquiv StableInfinityOwner.PresentedCategory
                        (1 : ℤ)).unitIso.inv.app _ ∧
                    (traceAnalyticStableInfinityCategory
                      .invRotatedCofiberShortComplex morphism).g =
                      morphism :=
  fun morphism =>
    And.intro
      (traceAnalyticStableInfinityCategory_cofiberShortComplex_f morphism)
      (And.intro
        (traceAnalyticStableInfinityCategory_cofiberShortComplex_g morphism)
        (And.intro
          (traceAnalyticStableInfinityCategory_fiberShortComplex_f morphism)
          (And.intro
            (traceAnalyticStableInfinityCategory_fiberShortComplex_g morphism)
            (And.intro
              (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplex_f
                morphism)
              (And.intro
                (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplex_g
                  morphism)
                (And.intro
                  (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplex_f
                    morphism)
                  (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplex_g
                    morphism)))))))

end AnalyticMotives
end LFunctions
end Boundary
