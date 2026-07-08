import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.CancellationLaws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.CancellationPayload.Owner

/-!
# Top-root named unstable input cancellation payload
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes descent-channel cancellation endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableDescentChannelIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- The root exposes descent-channel inverse-hom cancellation endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles :=
  TraceAnalyticMotive.unstableDescentChannelIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- The root exposes interval-Fubini cancellation endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- The root exposes interval-Fubini inverse-hom cancellation endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- The root exposes Tate-weight-drop cancellation endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableTateWeightDropIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- The root exposes Tate-weight-drop inverse-hom cancellation endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles :=
  TraceAnalyticMotive.unstableTateWeightDropIso_inv_comp_hom_endpointImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
