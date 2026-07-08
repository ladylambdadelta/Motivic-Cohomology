import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Payload.Endpoint.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.TraceCalculus.ImportedRectangles.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Endpoint ledger-count facts for triple forward words

This file specializes word-class endpoint length and ledger-count facts to the
two unstable forward-word parenthesizations of a composable triple.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Left-associated triple endpoint imported count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_length
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.leftAssociatedUnstableForwardWord.endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    triple.leftAssociatedUnstableForwardWord

/-- Right-associated triple endpoint imported count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_length
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    triple.rightAssociatedUnstableForwardWord

/-- Left-associated triple endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_certificateLedger_count
    triple.leftAssociatedUnstableForwardWord

/-- Right-associated triple endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointImportedRectangleCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointImportedRectangleCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_certificateLedger_count
    triple.rightAssociatedUnstableForwardWord

/-- Left-associated triple endpoint bookkeeping count is counted by the endpoint ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationWordClass.endpointTraceBookkeepingCount_eq_certificateLedger_count
    triple.leftAssociatedUnstableForwardWord

/-- Right-associated triple endpoint bookkeeping count is counted by the endpoint ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointTraceBookkeepingCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationWordClass.endpointTraceBookkeepingCount_eq_certificateLedger_count
    triple.rightAssociatedUnstableForwardWord

/-- Left-associated triple endpoint rewrite count is counted by the endpoint ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_endpointRewriteStepCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.leftAssociatedUnstableForwardWord.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationWordClass.endpointRewriteStepCount_eq_certificateLedger_count
    triple.leftAssociatedUnstableForwardWord

/-- Right-associated triple endpoint rewrite count is counted by the endpoint ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_endpointRewriteStepCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.endpointRewriteStepCount =
      triple.rightAssociatedUnstableForwardWord.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationWordClass.endpointRewriteStepCount_eq_certificateLedger_count
    triple.rightAssociatedUnstableForwardWord

end AnalyticMotives
end LFunctions
end Boundary
