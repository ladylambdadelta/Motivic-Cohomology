import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Associativity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Endpoint.LedgerCounts.Owner

/-!
# Ledger-count agreement under triple forward-word reassociation

This file records that reassociation preserves the endpoint rectangle-list
length and endpoint ledger counters of unstable forward-word triple composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Reassociation preserves endpoint rectangle-list length. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointImportedRectangles_length_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangles.length =
      triple.rightAssociatedUnstableForwardWord.endpointImportedRectangles.length :=
  congrArg
    List.length
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointImportedRectangles_eq
      triple)

/-- Reassociation preserves endpoint ledger imported-rectangle count. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointCertificateLedger_importedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.importedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointCertificateLedger_eq
      triple)

/-- Reassociation preserves endpoint ledger trace-bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointCertificateLedger_traceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.traceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointCertificateLedger_eq
      triple)

/-- Reassociation preserves endpoint ledger rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointCertificateLedger_rewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.rewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceLocalizationInputComposableTriple.associatedUnstableForwardWord_endpointCertificateLedger_eq
      triple)

end AnalyticMotives
end LFunctions
end Boundary
