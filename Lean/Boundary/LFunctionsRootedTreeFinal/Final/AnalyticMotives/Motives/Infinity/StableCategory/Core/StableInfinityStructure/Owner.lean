import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.ShortComplex.PerMorphism.Certificate.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.Owner

/-!
# Stable-infinity structure certificate

This file records the owner-level stable-infinity structure carried by the
concrete analytic motive presentation.  It packages the quasicategory, Verdier
localization, pointed shifted homotopy category, triangulated homotopy category,
global fiber/cofiber stability, and the certified short-complex calculus for
each morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The constructed analytic stable-infinity category has the full owner-level
stable structure currently available in the lane: quasicategory presentation,
Verdier localization, pointed shifted homotopy category, suspension-loop
equivalence, triangulated homotopy category, global stability, and the
per-morphism certified short-complex calculus. -/
theorem traceAnalyticStableInfinityCategory_actual_stable_infinity_structure :
    Quasicategory TraceAnalyticStableMotiveQuasicategory ∧
      TraceAnalyticStableMotiveQuasicategory.quotientFunctor.IsLocalization
        TraceAnalyticStableMotiveQuasicategory.invertedMorphisms ∧
        HasZeroObject
          TraceAnalyticStableInfinityCategory.HomotopyCategory ∧
          HasShift
            TraceAnalyticStableInfinityCategory.HomotopyCategory
            ℤ ∧
            traceAnalyticStableInfinityCategory.suspensionLoopEquivalence =
              shiftEquiv
                TraceAnalyticStableInfinityCategory.HomotopyCategory
                (1 : ℤ) ∧
              IsTriangulated
                TraceAnalyticStableInfinityCategory.HomotopyCategory ∧
                traceAnalyticStableInfinityCategory_global_stability_certificate ∧
                  ∀ {source target :
                      TraceAnalyticStableInfinityCategory.HomotopyCategory}
                    (morphism : source ⟶ target)
                    (leftProbe :
                      TraceAnalyticStableInfinityCategory
                        .HomotopyCategoryᵒᵖ)
                    (rightProbe :
                      TraceAnalyticStableInfinityCategory
                        .HomotopyCategory),
                    traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_certificate
                      morphism
                      leftProbe
                      rightProbe :=
  And.intro
    traceAnalyticStableInfinityCategory.quasicategory
    (And.intro
      traceAnalyticStableInfinityCategory.localization
      (And.intro
        traceAnalyticStableInfinityCategory.zeroObject
        (And.intro
          traceAnalyticStableInfinityCategory.shift
          (And.intro
            traceAnalyticStableInfinityCategory
              .suspensionLoopEquivalence_eq_shiftEquiv
            (And.intro
              traceAnalyticStableInfinityCategory.triangulated
              (And.intro
                traceAnalyticStableInfinityCategory_global_stability_certificate
                (fun morphism leftProbe rightProbe =>
                  traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_certificate
                    morphism
                    leftProbe
                    rightProbe)))))))

end AnalyticMotives
end LFunctions
end Boundary
