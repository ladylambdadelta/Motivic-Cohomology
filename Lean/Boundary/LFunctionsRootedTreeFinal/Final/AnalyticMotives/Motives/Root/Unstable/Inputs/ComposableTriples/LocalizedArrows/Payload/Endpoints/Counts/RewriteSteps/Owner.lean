import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoints.Counts.RewriteSteps.Owner

/-!
# Motive-root endpoint rewrite-step counts of localized-arrow triple composites

This file exposes source and target rewrite-step count projections for the two
named localized-forward-arrow triple composites through the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated localized-arrow source rewrite-step count. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.localizedForwardArrow.sourceRewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceRewriteStepCount
    triple

/-- Motive-root wrapper: left-associated localized-arrow target rewrite-step count. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.localizedForwardArrow.targetRewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetRewriteStepCount
    triple

/-- Motive-root wrapper: right-associated localized-arrow source rewrite-step count. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.localizedForwardArrow.sourceRewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceRewriteStepCount
    triple

/-- Motive-root wrapper: right-associated localized-arrow target rewrite-step count. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.localizedForwardArrow.targetRewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetRewriteStepCount
    triple

end AnalyticMotives
end LFunctions
end Boundary
