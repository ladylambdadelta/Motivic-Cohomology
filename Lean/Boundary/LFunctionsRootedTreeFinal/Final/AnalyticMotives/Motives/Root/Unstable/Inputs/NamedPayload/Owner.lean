import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.EndpointPayload.Owner

/-!
# Motive-root named unstable input payload
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom endpoint rectangles are source followed by target. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangles
    source
    target

/-- Interval-Fubini unstable hom endpoint rectangles are source followed by target. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangles
    source
    target

/-- Tate-weight-drop unstable hom endpoint rectangles are source followed by target. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangles
    source
    target

/-- Descent-channel unstable hom endpoint count is source count plus target count. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangleCount
    source
    target

/-- Interval-Fubini unstable hom endpoint count is source count plus target count. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangleCount
    source
    target

/-- Tate-weight-drop unstable hom endpoint count is source count plus target count. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangleCount
    source
    target

/-- Descent-channel unstable hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini unstable hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop unstable hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- Descent-channel unstable hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel unstable hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini unstable hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop unstable hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
