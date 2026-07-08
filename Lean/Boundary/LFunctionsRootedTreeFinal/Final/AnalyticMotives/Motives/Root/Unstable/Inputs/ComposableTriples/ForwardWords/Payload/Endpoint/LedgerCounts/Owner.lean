import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Endpoint.LedgerCounts.Owner

/-!
# Motive-root endpoint ledger-count facts for triple forward words

This file exposes endpoint length and ledger-count facts for unstable
forward-word triple composites through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated endpoint imported count is the endpoint-list length. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_length
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.leftAssociatedUnstableForwardWord.endpointImportedRectangles.length :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_length
    triple

/-- Motive-root wrapper: right-associated endpoint imported count is the endpoint-list length. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_length
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.endpointImportedRectangles.length :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_length
    triple

/-- Motive-root wrapper: left-associated endpoint imported count is counted by the ledger. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: right-associated endpoint imported count is counted by the ledger. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: left-associated endpoint bookkeeping count is counted by the ledger. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointTraceBookkeepingCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: right-associated endpoint bookkeeping count is counted by the ledger. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointTraceBookkeepingCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: left-associated endpoint rewrite count is counted by the ledger. -/
theorem TraceAnalyticMotive.leftAssociatedUnstableForwardWord_endpointRewriteStepCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointRewriteStepCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: right-associated endpoint rewrite count is counted by the ledger. -/
theorem TraceAnalyticMotive.rightAssociatedUnstableForwardWord_endpointRewriteStepCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointRewriteStepCount_eq_certificateLedger_count
    triple

end AnalyticMotives
end LFunctions
end Boundary
