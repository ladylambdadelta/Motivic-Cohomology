import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ZeroComposition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Fiber.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.CofiberRotations.ZeroComposition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Owner

/-!
# Global per-morphism zero-composition fields

This file bundles the zero fields for the four canonical short complexes
attached to one morphism in the analytic stable category: cofiber, fiber,
rotated cofiber, and inverse-rotated cofiber.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- For every morphism, the cofiber, fiber, rotated cofiber, and
inverse-rotated cofiber short complexes carry their canonical zero-composition
fields. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_zeroComposition :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target),
      (traceAnalyticStableInfinityCategory
        .cofiberShortComplex morphism).zero =
          traceAnalyticStableInfinityCategory
            .cofiber_morphism_comp_cocone morphism ∧
        (traceAnalyticStableInfinityCategory_fiberShortComplex
          morphism).zero =
            traceAnalyticStableInfinityCategory
              .fiberMap_comp_morphism morphism ∧
          (traceAnalyticStableInfinityCategory
            .rotatedCofiberShortComplex morphism).zero =
              traceAnalyticStableInfinityCategory
                .distinguishedTriangle_mor₁_comp_mor₂
                (traceAnalyticStableInfinityCategory.rotatedCofiberTriangle
                  morphism)
                (traceAnalyticStableInfinityCategory
                  .rotatedCofiberTriangle_distinguished morphism) ∧
            (traceAnalyticStableInfinityCategory
              .invRotatedCofiberShortComplex morphism).zero =
                traceAnalyticStableInfinityCategory
                  .distinguishedTriangle_mor₁_comp_mor₂
                  (traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
                    morphism)
                  (traceAnalyticStableInfinityCategory
                    .invRotatedCofiberTriangle_distinguished morphism) :=
  fun morphism =>
    And.intro
      (traceAnalyticStableInfinityCategory_cofiberShortComplex_zero
        morphism)
      (And.intro
        (traceAnalyticStableInfinityCategory_fiberShortComplex_zero
          morphism)
        (And.intro
          (traceAnalyticStableInfinityCategory_rotatedCofiberShortComplex_zero
            morphism)
          (traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplex_zero
            morphism)))

end AnalyticMotives
end LFunctions
end Boundary
