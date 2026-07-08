import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Associativity.LedgerCounts.Owner

/-!
# Public source and target ledger-counter agreement under reassociation

This file exposes source and target certificate-ledger counter agreement under
localized-forward-arrow reassociation through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: reassociation preserves source ledger imported-rectangle count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_sourceCertificateLedger_importedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger.importedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceCertificateLedger_importedRectangleCount_eq
    triple

/-- Public wrapper: reassociation preserves target ledger imported-rectangle count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_targetCertificateLedger_importedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger.importedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_targetCertificateLedger_importedRectangleCount_eq
    triple

/-- Public wrapper: reassociation preserves source ledger trace-bookkeeping count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_sourceCertificateLedger_traceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger.traceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceCertificateLedger_traceBookkeepingCount_eq
    triple

/-- Public wrapper: reassociation preserves target ledger trace-bookkeeping count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_targetCertificateLedger_traceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger.traceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_targetCertificateLedger_traceBookkeepingCount_eq
    triple

/-- Public wrapper: reassociation preserves source ledger rewrite-step count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_sourceCertificateLedger_rewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger.rewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_sourceCertificateLedger_rewriteStepCount_eq
    triple

/-- Public wrapper: reassociation preserves target ledger rewrite-step count. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_targetCertificateLedger_rewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger.rewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_targetCertificateLedger_rewriteStepCount_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
