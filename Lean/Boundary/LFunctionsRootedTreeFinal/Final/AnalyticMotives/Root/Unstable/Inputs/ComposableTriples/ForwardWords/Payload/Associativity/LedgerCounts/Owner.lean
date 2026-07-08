import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Associativity.LedgerCounts.Owner

/-!
# Public ledger-count agreement under triple forward-word reassociation

This file exposes endpoint rectangle-list length and endpoint ledger counter
agreement under reassociation through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: reassociation preserves endpoint rectangle-list length. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_endpointImportedRectangles_length_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangles.length =
      triple.rightAssociatedUnstableForwardWord.endpointImportedRectangles.length :=
  TraceAnalyticMotive.associatedUnstableForwardWord_endpointImportedRectangles_length_eq
    triple

/-- Public wrapper: reassociation preserves endpoint ledger imported-rectangle count. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_endpointCertificateLedger_importedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.importedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.associatedUnstableForwardWord_endpointCertificateLedger_importedRectangleCount_eq
    triple

/-- Public wrapper: reassociation preserves endpoint ledger trace-bookkeeping count. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_endpointCertificateLedger_traceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.traceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.associatedUnstableForwardWord_endpointCertificateLedger_traceBookkeepingCount_eq
    triple

/-- Public wrapper: reassociation preserves endpoint ledger rewrite-step count. -/
theorem AnalyticMotivesRoot.associatedUnstableForwardWord_endpointCertificateLedger_rewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.rewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.associatedUnstableForwardWord_endpointCertificateLedger_rewriteStepCount_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
