import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Localization.Projections.Owner

/-!
# Top-root localization projections

This file exposes the hom and inverse projections of the six calculus
localization isomorphisms under the public analytic-motives root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes descent channel localization. -/
theorem AnalyticMotivesRoot.descentChannelIso_hom
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentChannelIso source target).hom =
      TraceLocalizationInput.descentChannelForwardArrow source target :=
  TraceAnalyticMotive.descentChannelIso_hom
    source
    target

/-- The analytic-motives root exposes descent refinement localization. -/
theorem AnalyticMotivesRoot.descentRefinementIso_hom
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentRefinementIso source target).hom =
      TraceLocalizationInput.descentRefinementForwardArrow source target :=
  TraceAnalyticMotive.descentRefinementIso_hom
    source
    target

/-- The analytic-motives root exposes descent schedule localization. -/
theorem AnalyticMotivesRoot.descentScheduleIso_hom
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentScheduleIso source target).hom =
      TraceLocalizationInput.descentScheduleForwardArrow source target :=
  TraceAnalyticMotive.descentScheduleIso_hom
    source
    target

/-- The analytic-motives root exposes interval Stokes localization. -/
theorem AnalyticMotivesRoot.intervalStokesIso_hom
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalStokesIso source target).hom =
      TraceLocalizationInput.intervalStokesForwardArrow source target :=
  TraceAnalyticMotive.intervalStokesIso_hom
    source
    target

/-- The analytic-motives root exposes interval Fubini localization. -/
theorem AnalyticMotivesRoot.intervalFubiniIso_hom
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalFubiniIso source target).hom =
      TraceLocalizationInput.intervalFubiniForwardArrow source target :=
  TraceAnalyticMotive.intervalFubiniIso_hom
    source
    target

/-- The analytic-motives root exposes Tate weight-drop localization. -/
theorem AnalyticMotivesRoot.tateWeightDropIso_hom
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.tateWeightDropIso source target).hom =
      TraceLocalizationInput.tateWeightDropForwardArrow source target :=
  TraceAnalyticMotive.tateWeightDropIso_hom
    source
    target

/-- The analytic-motives root exposes descent channel inverse localization. -/
theorem AnalyticMotivesRoot.descentChannelIso_inv
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentChannelIso source target).inv =
      TraceLocalizationInput.descentChannelInverseArrow source target :=
  TraceAnalyticMotive.descentChannelIso_inv
    source
    target

/-- The analytic-motives root exposes descent refinement inverse localization. -/
theorem AnalyticMotivesRoot.descentRefinementIso_inv
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentRefinementIso source target).inv =
      TraceLocalizationInput.descentRefinementInverseArrow source target :=
  TraceAnalyticMotive.descentRefinementIso_inv
    source
    target

/-- The analytic-motives root exposes descent schedule inverse localization. -/
theorem AnalyticMotivesRoot.descentScheduleIso_inv
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentScheduleIso source target).inv =
      TraceLocalizationInput.descentScheduleInverseArrow source target :=
  TraceAnalyticMotive.descentScheduleIso_inv
    source
    target

/-- The analytic-motives root exposes interval Stokes inverse localization. -/
theorem AnalyticMotivesRoot.intervalStokesIso_inv
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalStokesIso source target).inv =
      TraceLocalizationInput.intervalStokesInverseArrow source target :=
  TraceAnalyticMotive.intervalStokesIso_inv
    source
    target

/-- The analytic-motives root exposes interval Fubini inverse localization. -/
theorem AnalyticMotivesRoot.intervalFubiniIso_inv
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalFubiniIso source target).inv =
      TraceLocalizationInput.intervalFubiniInverseArrow source target :=
  TraceAnalyticMotive.intervalFubiniIso_inv
    source
    target

/-- The analytic-motives root exposes Tate weight-drop inverse localization. -/
theorem AnalyticMotivesRoot.tateWeightDropIso_inv
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.tateWeightDropIso source target).inv =
      TraceLocalizationInput.tateWeightDropInverseArrow source target :=
  TraceAnalyticMotive.tateWeightDropIso_inv
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
