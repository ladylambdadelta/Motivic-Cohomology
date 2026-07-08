import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Associativity.LedgerCounts.Owner

/-!
# Motive-root ledger-count agreement under triple forward-word reassociation

This file exposes endpoint rectangle-list length and endpoint ledger counter
agreement under reassociation through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: reassociation preserves endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_endpointImportedRectangles_length_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangles.length =
      triple.rightAssociatedUnstableForwardWord.endpointImportedRectangles.length :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointImportedRectangles_length_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint ledger imported-rectangle count. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_endpointCertificateLedger_importedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.importedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointCertificateLedger_importedRectangleCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint ledger trace-bookkeeping count. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_endpointCertificateLedger_traceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.traceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointCertificateLedger_traceBookkeepingCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves endpoint ledger rewrite-step count. -/
theorem TraceAnalyticMotive.associatedUnstableForwardWord_endpointCertificateLedger_rewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.rewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointCertificateLedger_rewriteStepCount_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
