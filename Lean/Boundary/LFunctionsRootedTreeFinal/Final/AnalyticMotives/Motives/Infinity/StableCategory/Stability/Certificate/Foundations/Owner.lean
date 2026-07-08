import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Presentation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Preadditive.Owner

/-!
# Foundational certificate for analytic stable motives

This file bundles the foundational owner-level fields of the concrete analytic
stable-infinity category before the cofiber/fiber stability consequences are
used downstream.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The concrete analytic stable-infinity category is presented by the
analytic stable motive Verdier quotient, carries the analytic stable nerve,
localization, additive, pointed, shifted, pretriangulated, and triangulated
structures, and has the stable distinguished triangles. -/
theorem traceAnalyticStableInfinityCategory_foundational_certificate :
    StableInfinityOwner.PresentedCategory =
        TraceAnalyticStableMotiveCategory ∧
      TraceAnalyticStableMotiveQuasicategory =
          CategoryTheory.nerve TraceAnalyticStableMotiveCategory ∧
        traceAnalyticStableInfinityCategory.quasicategory =
            TraceAnalyticStableMotiveQuasicategory.quasicategory ∧
          traceAnalyticStableInfinityCategory.localization =
              TraceAnalyticStableMotiveQuasicategory.isLocalization ∧
            traceAnalyticStableInfinityCategory.preadditive =
                TraceAnalyticStableMotiveCategory.preadditiveStructure ∧
              traceAnalyticStableInfinityCategory.zeroObject =
                  traceAnalyticStableInfinityCategory_isPointed ∧
                traceAnalyticStableInfinityCategory.shift =
                    TraceAnalyticStableMotiveQuasicategory
                      .hasShiftStructure ∧
                  traceAnalyticStableInfinityCategory.quotientCommShift =
                      TraceAnalyticStableMotiveCategory
                        .quotientFunctorCommShift ∧
                    traceAnalyticStableInfinityCategory.pretriangulated =
                        TraceAnalyticStableMotiveQuasicategory
                          .pretriangulatedStructure ∧
                      traceAnalyticStableInfinityCategory.triangulated =
                          TraceAnalyticStableMotiveQuasicategory
                            .triangulatedStructure ∧
                        traceAnalyticStableInfinityCategory
                            .distinguishedTriangles =
                          TraceAnalyticStableMotiveQuasicategory
                            .distinguishedTriangles :=
  And.intro
    traceAnalyticStableInfinityCategory_presentedCategory_eq
    (And.intro
      traceAnalyticStableInfinityCategory_quasicategory_eq_nerve
      (And.intro
        rfl
        (And.intro
          rfl
          (And.intro
            rfl
            (And.intro
              rfl
              (And.intro
                rfl
                (And.intro
                  rfl
                  (And.intro
                    rfl
                    (And.intro
                      rfl
                      rfl)))))))))

end AnalyticMotives
end LFunctions
end Boundary
