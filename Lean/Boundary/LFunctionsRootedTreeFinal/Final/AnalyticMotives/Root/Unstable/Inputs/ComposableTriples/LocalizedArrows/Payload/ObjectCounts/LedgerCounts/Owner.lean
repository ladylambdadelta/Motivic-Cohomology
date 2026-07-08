import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.ObjectCounts.LedgerCounts.Owner

/-!
# Public object-level ledger counts of localized-arrow triple composites

This file exposes object-level ledger-count facts for localized-forward-arrow
triple composites through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: left-associated source imported count is counted by the first source ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.sourceObject.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount_eq_certificateLedger_count
    triple

/-- Public wrapper: left-associated target imported count is counted by the third target ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.targetObject.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount_eq_certificateLedger_count
    triple

/-- Public wrapper: right-associated source imported count is counted by the first source ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.sourceObject.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount_eq_certificateLedger_count
    triple

/-- Public wrapper: right-associated target imported count is counted by the third target ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.targetObject.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount_eq_certificateLedger_count
    triple

/-- Public wrapper: left-associated source bookkeeping count is counted by the first source ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.sourceObject.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount_eq_certificateLedger_count
    triple

/-- Public wrapper: left-associated target bookkeeping count is counted by the third target ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.targetObject.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount_eq_certificateLedger_count
    triple

/-- Public wrapper: right-associated source bookkeeping count is counted by the first source ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.sourceObject.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount_eq_certificateLedger_count
    triple

/-- Public wrapper: right-associated target bookkeeping count is counted by the third target ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.targetObject.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount_eq_certificateLedger_count
    triple

/-- Public wrapper: left-associated source rewrite-step count is counted by the first source ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.sourceObject.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount_eq_certificateLedger_count
    triple

/-- Public wrapper: left-associated target rewrite-step count is counted by the third target ledger. -/
theorem AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.targetObject.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount_eq_certificateLedger_count
    triple

/-- Public wrapper: right-associated source rewrite-step count is counted by the first source ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.sourceObject.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount_eq_certificateLedger_count
    triple

/-- Public wrapper: right-associated target rewrite-step count is counted by the third target ledger. -/
theorem AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.targetObject.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount_eq_certificateLedger_count
    triple

end AnalyticMotives
end LFunctions
end Boundary
