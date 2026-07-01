import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Arrows.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.ByKind.Owner

/-!
# Cancellation laws for named by-kind localized isomorphisms

This file records the hom-inverse and inverse-hom cancellation laws for each
named by-kind localized isomorphism.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel localized isomorphism hom followed by inverse is identity. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).sourceObject :=
  TraceLocalizationInput.descentChannelForward_comp_inverse source target

/-- Descent-channel localized isomorphism inverse followed by hom is identity. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).targetObject :=
  TraceLocalizationInput.descentChannelInverse_comp_forward source target

/-- Descent-refinement localized isomorphism hom followed by inverse is identity. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).sourceObject :=
  TraceLocalizationInput.descentRefinementForward_comp_inverse source target

/-- Descent-refinement localized isomorphism inverse followed by hom is identity. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).targetObject :=
  TraceLocalizationInput.descentRefinementInverse_comp_forward source target

/-- Descent-schedule localized isomorphism hom followed by inverse is identity. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).sourceObject :=
  TraceLocalizationInput.descentScheduleForward_comp_inverse source target

/-- Descent-schedule localized isomorphism inverse followed by hom is identity. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).targetObject :=
  TraceLocalizationInput.descentScheduleInverse_comp_forward source target

/-- Interval-Stokes localized isomorphism hom followed by inverse is identity. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).sourceObject :=
  TraceLocalizationInput.intervalStokesForward_comp_inverse source target

/-- Interval-Stokes localized isomorphism inverse followed by hom is identity. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).targetObject :=
  TraceLocalizationInput.intervalStokesInverse_comp_forward source target

/-- Interval-Fubini localized isomorphism hom followed by inverse is identity. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).sourceObject :=
  TraceLocalizationInput.intervalFubiniForward_comp_inverse source target

/-- Interval-Fubini localized isomorphism inverse followed by hom is identity. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).targetObject :=
  TraceLocalizationInput.intervalFubiniInverse_comp_forward source target

/-- Tate-weight-drop localized isomorphism hom followed by inverse is identity. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject :=
  TraceLocalizationInput.tateWeightDropForward_comp_inverse source target

/-- Tate-weight-drop localized isomorphism inverse followed by hom is identity. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).targetObject :=
  TraceLocalizationInput.tateWeightDropInverse_comp_forward source target

end AnalyticMotives
end LFunctions
end Boundary
