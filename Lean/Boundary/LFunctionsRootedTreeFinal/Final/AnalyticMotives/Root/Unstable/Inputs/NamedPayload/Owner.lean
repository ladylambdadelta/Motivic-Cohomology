import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.EndpointPayload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.NamedPayload.Owner

/-!
# Top-root named unstable input payload
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes descent-channel unstable endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointImportedRectangles
    source
    target

/-- The analytic-motives root exposes interval-Fubini unstable endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointImportedRectangles
    source
    target

/-- The analytic-motives root exposes Tate-weight-drop unstable endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointImportedRectangles
    source
    target

/-- The analytic-motives root exposes descent-channel unstable endpoint counts. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointImportedRectangleCount
    source
    target

/-- The analytic-motives root exposes interval-Fubini unstable endpoint counts. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointImportedRectangleCount
    source
    target

/-- The analytic-motives root exposes Tate-weight-drop unstable endpoint counts. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointImportedRectangleCount
    source
    target

/-- The analytic-motives root exposes descent-channel unstable count-as-length. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The analytic-motives root exposes interval-Fubini unstable count-as-length. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The analytic-motives root exposes Tate-weight-drop unstable count-as-length. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes descent-channel unstable imported-rectangle ledger counts. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes interval-Fubini unstable imported-rectangle ledger counts. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes Tate-weight-drop unstable imported-rectangle ledger counts. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes descent-channel unstable imported-rectangle ledger lists. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes interval-Fubini unstable imported-rectangle ledger lists. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- The root exposes Tate-weight-drop unstable imported-rectangle ledger lists. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
