import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Associativity.Owner

/-!
# Source and target ledger-counter agreement under localized-arrow reassociation

This file records that reassociation preserves the source and target
certificate-ledger counters of named localized-forward-arrow triple composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Reassociation preserves source ledger imported-rectangle count. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceCertificateLedger_importedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger.importedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger.importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceCertificateLedger_eq
      triple)

/-- Reassociation preserves target ledger imported-rectangle count. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetCertificateLedger_importedRectangleCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger.importedRectangleCount =
      triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger.importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetCertificateLedger_eq
      triple)

/-- Reassociation preserves source ledger trace-bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceCertificateLedger_traceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger.traceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger.traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceCertificateLedger_eq
      triple)

/-- Reassociation preserves target ledger trace-bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetCertificateLedger_traceBookkeepingCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger.traceBookkeepingCount =
      triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger.traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetCertificateLedger_eq
      triple)

/-- Reassociation preserves source ledger rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceCertificateLedger_rewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceCertificateLedger.rewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.sourceCertificateLedger.rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_sourceCertificateLedger_eq
      triple)

/-- Reassociation preserves target ledger rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetCertificateLedger_rewriteStepCount_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetCertificateLedger.rewriteStepCount =
      triple.rightAssociatedLocalizedForwardArrow.targetCertificateLedger.rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_targetCertificateLedger_eq
      triple)

end AnalyticMotives
end LFunctions
end Boundary
