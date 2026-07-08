import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.CancellationLaws.Owner

/-!
# Motive-root named unstable input cancellation payload
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- Descent-channel unstable inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- Interval-Fubini unstable hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- Interval-Fubini unstable inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- Tate-weight-drop unstable hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- Tate-weight-drop unstable inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
