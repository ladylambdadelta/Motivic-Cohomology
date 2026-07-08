import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Owner

/-!
# Presented-category certificate for analytic stable motives

This file records that the owner-level stable-infinity package is presented by
the concrete analytic Verdier quotient already constructed in the stabilization
lane.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package's presented category is the analytic stable motive Verdier
quotient. -/
theorem traceAnalyticStableInfinityCategory_presentedCategory_eq :
    StableInfinityOwner.PresentedCategory =
      TraceAnalyticStableMotiveCategory :=
  rfl

/-- The package's quasicategory is the nerve of the analytic stable motive
Verdier quotient. -/
theorem traceAnalyticStableInfinityCategory_quasicategory_eq_nerve :
    TraceAnalyticStableMotiveQuasicategory =
      CategoryTheory.nerve TraceAnalyticStableMotiveCategory :=
  rfl

/-- The package's quotient functor is the analytic Verdier quotient functor. -/
theorem traceAnalyticStableInfinityCategory_quotientFunctor_eq :
    TraceAnalyticStableMotiveQuasicategory.quotientFunctor =
      TraceAnalyticStableMotiveCategory.quotientFunctor :=
  rfl

/-- The package's inverted morphism class is the analytic stable-null
morphism class. -/
theorem traceAnalyticStableInfinityCategory_invertedMorphisms_eq :
    TraceAnalyticStableMotiveQuasicategory.invertedMorphisms =
      TraceAnalyticStableMotiveCategory.invertedMorphisms :=
  rfl

/-- The package's localization field is the Verdier localization theorem for
analytic stable motives. -/
theorem traceAnalyticStableInfinityCategory_localization_eq_stable :
    traceAnalyticStableInfinityCategory.localization =
      TraceAnalyticStableMotiveCategory.isLocalization :=
  rfl

/-- The package's distinguished triangles are the distinguished triangles of
the analytic stable motive Verdier quotient. -/
theorem traceAnalyticStableInfinityCategory_distinguishedTriangles_eq_stable :
    traceAnalyticStableInfinityCategory.distinguishedTriangles =
      TraceAnalyticStableMotiveCategory.distinguishedTriangles :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
