import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.ShortComplex.PerMorphism.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.YonedaExact.PerMorphism.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.ZeroComposition.PerMorphism.Owner

/-!
# Global per-morphism short-complex certificate

This file packages the three owner-level facts needed by downstream
stable-category arguments: the four canonical short complexes have the expected
maps, their consecutive maps compose to zero, and their Yoneda images are exact.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- For every morphism, the cofiber, fiber, rotated cofiber, and
inverse-rotated cofiber short complexes carry the full certified short-complex
package: map shape, zero composition, and covariant/contravariant Yoneda
exactness. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_certificate :
    ∀ {source target : StableInfinityOwner.PresentedCategory}
      (morphism : source ⟶ target)
      (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
      (rightProbe : StableInfinityOwner.PresentedCategory),
      traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape
          morphism ∧
        traceAnalyticStableInfinityCategory_global_perMorphism_zeroComposition
          morphism ∧
          traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact
            morphism
            leftProbe
            rightProbe :=
  fun morphism leftProbe rightProbe =>
    And.intro
      (traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape
        morphism)
      (And.intro
        (traceAnalyticStableInfinityCategory_global_perMorphism_zeroComposition
          morphism)
        (traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact
          morphism
          leftProbe
          rightProbe))

end AnalyticMotives
end LFunctions
end Boundary
