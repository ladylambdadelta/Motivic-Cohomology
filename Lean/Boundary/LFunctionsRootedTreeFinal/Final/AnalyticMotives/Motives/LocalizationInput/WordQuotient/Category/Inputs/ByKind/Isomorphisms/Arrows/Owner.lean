import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Owner

/-!
# Arrows of named input-level localized isomorphisms

This file records that the hom and inverse arrows of each named by-kind
localized isomorphism are the corresponding named forward and inverse arrows.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The descent-channel localized isomorphism hom is the descent-channel forward arrow. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso source target).hom =
      TraceLocalizationInput.descentChannelForwardArrow source target :=
  rfl

/-- The descent-channel localized isomorphism inverse is the descent-channel inverse arrow. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso source target).inv =
      TraceLocalizationInput.descentChannelInverseArrow source target :=
  rfl

/-- The descent-refinement localized isomorphism hom is the descent-refinement forward arrow. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom =
      TraceLocalizationInput.descentRefinementForwardArrow source target :=
  rfl

/-- The descent-refinement localized isomorphism inverse is the descent-refinement inverse arrow. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv =
      TraceLocalizationInput.descentRefinementInverseArrow source target :=
  rfl

/-- The descent-schedule localized isomorphism hom is the descent-schedule forward arrow. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom =
      TraceLocalizationInput.descentScheduleForwardArrow source target :=
  rfl

/-- The descent-schedule localized isomorphism inverse is the descent-schedule inverse arrow. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv =
      TraceLocalizationInput.descentScheduleInverseArrow source target :=
  rfl

/-- The interval-Stokes localized isomorphism hom is the interval-Stokes forward arrow. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom =
      TraceLocalizationInput.intervalStokesForwardArrow source target :=
  rfl

/-- The interval-Stokes localized isomorphism inverse is the interval-Stokes inverse arrow. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv =
      TraceLocalizationInput.intervalStokesInverseArrow source target :=
  rfl

/-- The interval-Fubini localized isomorphism hom is the interval-Fubini forward arrow. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom =
      TraceLocalizationInput.intervalFubiniForwardArrow source target :=
  rfl

/-- The interval-Fubini localized isomorphism inverse is the interval-Fubini inverse arrow. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv =
      TraceLocalizationInput.intervalFubiniInverseArrow source target :=
  rfl

/-- The Tate-weight-drop localized isomorphism hom is the Tate-weight-drop forward arrow. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom =
      TraceLocalizationInput.tateWeightDropForwardArrow source target :=
  rfl

/-- The Tate-weight-drop localized isomorphism inverse is the Tate-weight-drop inverse arrow. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv =
      TraceLocalizationInput.tateWeightDropInverseArrow source target :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
