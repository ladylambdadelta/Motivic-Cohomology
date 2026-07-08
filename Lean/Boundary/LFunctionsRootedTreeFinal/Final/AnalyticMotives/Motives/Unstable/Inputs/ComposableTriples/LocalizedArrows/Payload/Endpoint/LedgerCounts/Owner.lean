import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Endpoint.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.TraceCalculus.ImportedRectangles.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Endpoint ledger-count facts for localized-arrow triple composites

This file specializes word-class endpoint length and ledger-count facts to the
two named localized-forward-arrow parenthesizations of a composable triple.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Left-associated localized-arrow endpoint imported count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_length
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    triple.leftAssociatedLocalizedForwardArrow

/-- Right-associated localized-arrow endpoint imported count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_length
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangles.length :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    triple.rightAssociatedLocalizedForwardArrow

/-- Left-associated localized-arrow endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_certificateLedger_count
    triple.leftAssociatedLocalizedForwardArrow

/-- Right-associated localized-arrow endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointImportedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_certificateLedger_count
    triple.rightAssociatedLocalizedForwardArrow

/-- Left-associated localized-arrow endpoint bookkeeping count is counted by the endpoint ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationWordClass.endpointTraceBookkeepingCount_eq_certificateLedger_count
    triple.leftAssociatedLocalizedForwardArrow

/-- Right-associated localized-arrow endpoint bookkeeping count is counted by the endpoint ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointTraceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationWordClass.endpointTraceBookkeepingCount_eq_certificateLedger_count
    triple.rightAssociatedLocalizedForwardArrow

/-- Left-associated localized-arrow endpoint rewrite count is counted by the endpoint ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.leftAssociatedLocalizedForwardArrow.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationWordClass.endpointRewriteStepCount_eq_certificateLedger_count
    triple.leftAssociatedLocalizedForwardArrow

/-- Right-associated localized-arrow endpoint rewrite count is counted by the endpoint ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_endpointRewriteStepCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.endpointRewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationWordClass.endpointRewriteStepCount_eq_certificateLedger_count
    triple.rightAssociatedLocalizedForwardArrow

end AnalyticMotives
end LFunctions
end Boundary
