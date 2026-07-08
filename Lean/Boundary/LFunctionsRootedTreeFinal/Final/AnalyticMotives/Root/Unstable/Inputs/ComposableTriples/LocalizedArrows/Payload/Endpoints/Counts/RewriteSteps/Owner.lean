import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoints.Counts.RewriteSteps.Owner

/-!
# Public endpoint rewrite-step counts of localized-arrow triple composites

This file exposes source and target rewrite-step count projections for the two
named localized-forward-arrow triple composites through the public
analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated localized-arrow source rewrite-step count. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.localizedForwardArrow.sourceRewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceRewriteStepCount
    triple

/-- Public wrapper: left-associated localized-arrow target rewrite-step count. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.localizedForwardArrow.targetRewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetRewriteStepCount
    triple

/-- Public wrapper: right-associated localized-arrow source rewrite-step count. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.localizedForwardArrow.sourceRewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceRewriteStepCount
    triple

/-- Public wrapper: right-associated localized-arrow target rewrite-step count. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.localizedForwardArrow.targetRewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetRewriteStepCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
