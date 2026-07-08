import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.NamedPayload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.CancellationLaws.Owner

/-!
# Top-root named unstable input cancellation laws
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes descent-channel unstable hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).sourceObject :=
  TraceAnalyticMotive.unstableDescentChannelIso_hom_comp_inv
    source
    target

/-- The root exposes descent-channel unstable inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).targetObject :=
  TraceAnalyticMotive.unstableDescentChannelIso_inv_comp_hom
    source
    target

/-- The root exposes descent-channel unstable categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom ≫
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject) :=
  TraceAnalyticMotive.unstableDescentChannelIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The root exposes descent-channel unstable categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv ≫
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject) :=
  TraceAnalyticMotive.unstableDescentChannelIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- The root exposes interval-Fubini unstable hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).sourceObject :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_hom_comp_inv
    source
    target

/-- The root exposes interval-Fubini unstable inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).targetObject :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_inv_comp_hom
    source
    target

/-- The root exposes interval-Fubini unstable categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom ≫
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject) :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The root exposes interval-Fubini unstable categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv ≫
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject) :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- The root exposes Tate-weight-drop unstable hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject :=
  TraceAnalyticMotive.unstableTateWeightDropIso_hom_comp_inv
    source
    target

/-- The root exposes Tate-weight-drop unstable inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).targetObject :=
  TraceAnalyticMotive.unstableTateWeightDropIso_inv_comp_hom
    source
    target

/-- The root exposes Tate-weight-drop unstable categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom ≫
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject) :=
  TraceAnalyticMotive.unstableTateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The root exposes Tate-weight-drop unstable categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv ≫
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject) :=
  TraceAnalyticMotive.unstableTateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
