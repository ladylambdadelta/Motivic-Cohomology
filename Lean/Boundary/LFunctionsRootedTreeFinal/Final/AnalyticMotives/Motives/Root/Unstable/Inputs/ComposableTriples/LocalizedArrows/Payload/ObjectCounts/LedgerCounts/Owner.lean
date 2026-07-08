import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.ObjectCounts.LedgerCounts.Owner

/-!
# Motive-root object-level ledger counts of localized-arrow triple composites

This file exposes object-level ledger-count facts for localized-forward-arrow
triple composites through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: left-associated source imported count is counted by the first source ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.sourceObject.certificateLedger.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: left-associated target imported count is counted by the third target ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.targetObject.certificateLedger.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: right-associated source imported count is counted by the first source ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.sourceObject.certificateLedger.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: right-associated target imported count is counted by the third target ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.targetObject.certificateLedger.importedRectangleCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: left-associated source bookkeeping count is counted by the first source ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.sourceObject.certificateLedger.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: left-associated target bookkeeping count is counted by the third target ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.targetObject.certificateLedger.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: right-associated source bookkeeping count is counted by the first source ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.sourceObject.certificateLedger.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: right-associated target bookkeeping count is counted by the third target ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.targetObject.certificateLedger.traceBookkeepingCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: left-associated source rewrite-step count is counted by the first source ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.sourceObject.certificateLedger.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: left-associated target rewrite-step count is counted by the third target ledger. -/
theorem TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.targetObject.certificateLedger.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: right-associated source rewrite-step count is counted by the first source ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.sourceObject.certificateLedger.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount_eq_certificateLedger_count
    triple

/-- Motive-root wrapper: right-associated target rewrite-step count is counted by the third target ledger. -/
theorem TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.targetObject.certificateLedger.rewriteStepCount :=
  TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount_eq_certificateLedger_count
    triple

end AnalyticMotives
end LFunctions
end Boundary
