import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Core structure projections for the analytic stable infinity category

This file records the bundled core categorical content of the assembled
analytic stable-infinity category.  The statement is deliberately only a
projection theorem: it does not identify this stable presentation with the
derived t-structure presentation or with an algebraic comparison target.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The assembled analytic stable-infinity category has exactly the core
structures supplied by the Verdier-localized analytic stable motive
quasicategory: localization, preadditivity, zero object, shifts,
pretriangulation, triangulation, and distinguished triangles. -/
theorem traceAnalyticStableInfinityCategory_core_structure :
    traceAnalyticStableInfinityCategory.quasicategory =
        TraceAnalyticStableMotiveQuasicategory.quasicategory ∧
      traceAnalyticStableInfinityCategory.localization =
          TraceAnalyticStableMotiveQuasicategory.isLocalization ∧
        traceAnalyticStableInfinityCategory.preadditive =
            TraceAnalyticStableMotiveCategory.preadditiveStructure ∧
          traceAnalyticStableInfinityCategory.zeroObject =
              TraceAnalyticStableMotiveCategory.zeroObjectStructure ∧
            traceAnalyticStableInfinityCategory.shift =
                TraceAnalyticStableMotiveQuasicategory.hasShiftStructure ∧
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
                rfl))))))

end AnalyticMotives
end LFunctions
end Boundary
