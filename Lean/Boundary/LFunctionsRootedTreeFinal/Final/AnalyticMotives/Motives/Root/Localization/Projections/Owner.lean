import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CalculusLocalization.Owner

/-!
# Motive-root localization projections

This file exposes the hom and inverse projections of the six calculus
localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The combined calculus localization exposes channel descent as an isomorphism. -/
theorem TraceAnalyticMotive.descentChannelIso_hom
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentChannelIso source target).hom =
      TraceLocalizationInput.descentChannelForwardArrow source target :=
  TraceCalculusLocalization.descentChannelIso_hom
    source
    target

/-- The combined calculus localization exposes refinement descent as an isomorphism. -/
theorem TraceAnalyticMotive.descentRefinementIso_hom
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentRefinementIso source target).hom =
      TraceLocalizationInput.descentRefinementForwardArrow source target :=
  TraceCalculusLocalization.descentRefinementIso_hom
    source
    target

/-- The combined calculus localization exposes schedule descent as an isomorphism. -/
theorem TraceAnalyticMotive.descentScheduleIso_hom
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentScheduleIso source target).hom =
      TraceLocalizationInput.descentScheduleForwardArrow source target :=
  TraceCalculusLocalization.descentScheduleIso_hom
    source
    target

/-- The combined calculus localization exposes interval Stokes as an isomorphism. -/
theorem TraceAnalyticMotive.intervalStokesIso_hom
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalStokesIso source target).hom =
      TraceLocalizationInput.intervalStokesForwardArrow source target :=
  TraceCalculusLocalization.intervalStokesIso_hom
    source
    target

/-- The combined calculus localization exposes interval Fubini as an isomorphism. -/
theorem TraceAnalyticMotive.intervalFubiniIso_hom
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalFubiniIso source target).hom =
      TraceLocalizationInput.intervalFubiniForwardArrow source target :=
  TraceCalculusLocalization.intervalFubiniIso_hom
    source
    target

/-- The combined calculus localization exposes Tate weight-drop as an isomorphism. -/
theorem TraceAnalyticMotive.tateWeightDropIso_hom
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.tateWeightDropIso source target).hom =
      TraceLocalizationInput.tateWeightDropForwardArrow source target :=
  TraceCalculusLocalization.tateWeightDropIso_hom
    source
    target

/-- The combined calculus localization exposes channel descent inverse arrow. -/
theorem TraceAnalyticMotive.descentChannelIso_inv
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentChannelIso source target).inv =
      TraceLocalizationInput.descentChannelInverseArrow source target :=
  TraceCalculusLocalization.descentChannelIso_inv
    source
    target

/-- The combined calculus localization exposes refinement descent inverse arrow. -/
theorem TraceAnalyticMotive.descentRefinementIso_inv
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentRefinementIso source target).inv =
      TraceLocalizationInput.descentRefinementInverseArrow source target :=
  TraceCalculusLocalization.descentRefinementIso_inv
    source
    target

/-- The combined calculus localization exposes schedule descent inverse arrow. -/
theorem TraceAnalyticMotive.descentScheduleIso_inv
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentScheduleIso source target).inv =
      TraceLocalizationInput.descentScheduleInverseArrow source target :=
  TraceCalculusLocalization.descentScheduleIso_inv
    source
    target

/-- The combined calculus localization exposes interval Stokes inverse arrow. -/
theorem TraceAnalyticMotive.intervalStokesIso_inv
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalStokesIso source target).inv =
      TraceLocalizationInput.intervalStokesInverseArrow source target :=
  TraceCalculusLocalization.intervalStokesIso_inv
    source
    target

/-- The combined calculus localization exposes interval Fubini inverse arrow. -/
theorem TraceAnalyticMotive.intervalFubiniIso_inv
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalFubiniIso source target).inv =
      TraceLocalizationInput.intervalFubiniInverseArrow source target :=
  TraceCalculusLocalization.intervalFubiniIso_inv
    source
    target

/-- The combined calculus localization exposes Tate weight-drop inverse arrow. -/
theorem TraceAnalyticMotive.tateWeightDropIso_inv
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.tateWeightDropIso source target).inv =
      TraceLocalizationInput.tateWeightDropInverseArrow source target :=
  TraceCalculusLocalization.tateWeightDropIso_inv
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
