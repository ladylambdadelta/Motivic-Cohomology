import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Descent.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Descent.Localization.Owner

/-!
# Descent and refinement localization

This file owns the descent/refinement localization for trace presheaves.

Analytically, this is where refinement invariance and local contour
decomposition are imposed as equivalences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open scoped CategoryTheory

/-- Channel descent has the named localized forward arrow as hom. -/
theorem TraceDescent.channelIso_hom
    (source target : QTraceExpression) :
    (TraceDescentLocalization.channelIso source target).hom =
      TraceLocalizationInput.descentChannelForwardArrow source target :=
  TraceDescentLocalization.channelIso_hom
    source
    target

/-- Channel descent has the named localized inverse arrow as inverse. -/
theorem TraceDescent.channelIso_inv
    (source target : QTraceExpression) :
    (TraceDescentLocalization.channelIso source target).inv =
      TraceLocalizationInput.descentChannelInverseArrow source target :=
  TraceDescentLocalization.channelIso_inv
    source
    target

/-- Channel descent hom followed by inverse is identity in the localized-word category. -/
theorem TraceDescent.channelIso_hom_comp_inv
    (source target : QTraceExpression) :
    (TraceDescentLocalization.channelIso source target).hom ≫
        (TraceDescentLocalization.channelIso source target).inv =
      𝟙 (TraceLocalizationInput.descentChannel source target).localizedSourceObject :=
  TraceDescentLocalization.channelIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Channel descent inverse followed by hom is identity in the localized-word category. -/
theorem TraceDescent.channelIso_inv_comp_hom
    (source target : QTraceExpression) :
    (TraceDescentLocalization.channelIso source target).inv ≫
        (TraceDescentLocalization.channelIso source target).hom =
      𝟙 (TraceLocalizationInput.descentChannel source target).localizedTargetObject :=
  TraceDescentLocalization.channelIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Refinement descent has the named localized forward arrow as hom. -/
theorem TraceDescent.refinementIso_hom
    (source target : QTraceExpression) :
    (TraceDescentLocalization.refinementIso source target).hom =
      TraceLocalizationInput.descentRefinementForwardArrow source target :=
  TraceDescentLocalization.refinementIso_hom
    source
    target

/-- Refinement descent has the named localized inverse arrow as inverse. -/
theorem TraceDescent.refinementIso_inv
    (source target : QTraceExpression) :
    (TraceDescentLocalization.refinementIso source target).inv =
      TraceLocalizationInput.descentRefinementInverseArrow source target :=
  TraceDescentLocalization.refinementIso_inv
    source
    target

/-- Refinement descent hom followed by inverse is identity in the localized-word category. -/
theorem TraceDescent.refinementIso_hom_comp_inv
    (source target : QTraceExpression) :
    (TraceDescentLocalization.refinementIso source target).hom ≫
        (TraceDescentLocalization.refinementIso source target).inv =
      𝟙 (TraceLocalizationInput.descentRefinement source target).localizedSourceObject :=
  TraceDescentLocalization.refinementIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Refinement descent inverse followed by hom is identity in the localized-word category. -/
theorem TraceDescent.refinementIso_inv_comp_hom
    (source target : QTraceExpression) :
    (TraceDescentLocalization.refinementIso source target).inv ≫
        (TraceDescentLocalization.refinementIso source target).hom =
      𝟙 (TraceLocalizationInput.descentRefinement source target).localizedTargetObject :=
  TraceDescentLocalization.refinementIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Schedule descent has the named localized forward arrow as hom. -/
theorem TraceDescent.scheduleIso_hom
    (source target : QTraceExpression) :
    (TraceDescentLocalization.scheduleIso source target).hom =
      TraceLocalizationInput.descentScheduleForwardArrow source target :=
  TraceDescentLocalization.scheduleIso_hom
    source
    target

/-- Schedule descent has the named localized inverse arrow as inverse. -/
theorem TraceDescent.scheduleIso_inv
    (source target : QTraceExpression) :
    (TraceDescentLocalization.scheduleIso source target).inv =
      TraceLocalizationInput.descentScheduleInverseArrow source target :=
  TraceDescentLocalization.scheduleIso_inv
    source
    target

/-- Schedule descent hom followed by inverse is identity in the localized-word category. -/
theorem TraceDescent.scheduleIso_hom_comp_inv
    (source target : QTraceExpression) :
    (TraceDescentLocalization.scheduleIso source target).hom ≫
        (TraceDescentLocalization.scheduleIso source target).inv =
      𝟙 (TraceLocalizationInput.descentSchedule source target).localizedSourceObject :=
  TraceDescentLocalization.scheduleIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Schedule descent inverse followed by hom is identity in the localized-word category. -/
theorem TraceDescent.scheduleIso_inv_comp_hom
    (source target : QTraceExpression) :
    (TraceDescentLocalization.scheduleIso source target).inv ≫
        (TraceDescentLocalization.scheduleIso source target).hom =
      𝟙 (TraceLocalizationInput.descentSchedule source target).localizedTargetObject :=
  TraceDescentLocalization.scheduleIso_inv_comp_hom_eq_categoryIdentity
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
