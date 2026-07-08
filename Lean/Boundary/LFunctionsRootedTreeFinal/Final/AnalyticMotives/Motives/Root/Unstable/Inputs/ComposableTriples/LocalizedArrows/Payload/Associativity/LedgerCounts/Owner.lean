import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Associativity.LedgerCounts.Owner

/-!
# Motive-root source and target ledger-counter agreement under reassociation

This file exposes source and target certificate-ledger counter agreement under
localized-forward-arrow reassociation through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: reassociation preserves source ledger imported-rectangle count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceCertificateLedger_importedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger.importedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceCertificateLedger_importedRectangleCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves target ledger imported-rectangle count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_targetCertificateLedger_importedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger.importedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetCertificateLedger_importedRectangleCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves source ledger trace-bookkeeping count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceCertificateLedger_traceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger.traceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceCertificateLedger_traceBookkeepingCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves target ledger trace-bookkeeping count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_targetCertificateLedger_traceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger.traceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetCertificateLedger_traceBookkeepingCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves source ledger rewrite-step count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceCertificateLedger_rewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger.rewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceCertificateLedger_rewriteStepCount_eq
    triple

/-- Motive-root wrapper: reassociation preserves target ledger rewrite-step count. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_targetCertificateLedger_rewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger.rewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetCertificateLedger_rewriteStepCount_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
