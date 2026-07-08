import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.NamedPayload.Owner

/-!
# Motive-root named unstable input cancellation laws
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom followed by inverse is identity. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).sourceObject :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv
    source
    target

/-- Descent-channel unstable inverse followed by hom is identity. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).targetObject :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom
    source
    target

/-- Descent-channel unstable hom followed by inverse is categorical identity. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom ≫
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject) :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Descent-channel unstable inverse followed by hom is categorical identity. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv ≫
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject) :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Interval-Fubini unstable hom followed by inverse is identity. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).sourceObject :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv
    source
    target

/-- Interval-Fubini unstable inverse followed by hom is identity. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).targetObject :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom
    source
    target

/-- Interval-Fubini unstable hom followed by inverse is categorical identity. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom ≫
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject) :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Interval-Fubini unstable inverse followed by hom is categorical identity. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv ≫
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject) :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Tate-weight-drop unstable hom followed by inverse is identity. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv
    source
    target

/-- Tate-weight-drop unstable inverse followed by hom is identity. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).targetObject :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom
    source
    target

/-- Tate-weight-drop unstable hom followed by inverse is categorical identity. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom ≫
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject) :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Tate-weight-drop unstable inverse followed by hom is categorical identity. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv ≫
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject) :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
