import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.ObjectCounts.Owner

/-!
# Object-level ledger counts of localized-arrow triple composites

This file records that the object-level endpoint counts of the two named
localized-forward-arrow triple composites are counted by the corresponding
endpoint object certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated source object imported count is counted by the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.sourceObject.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount
      triple)
    (TraceCorQObject.importedRectangleCount_eq_certificateLedger_count
      triple.first.sourceObject)

/-- The left-associated target object imported count is counted by the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.targetObject.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount
      triple)
    (TraceCorQObject.importedRectangleCount_eq_certificateLedger_count
      triple.third.targetObject)

/-- The right-associated source object imported count is counted by the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceImportedRectangleCount =
      triple.first.sourceObject.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceImportedRectangleObjectCount
      triple)
    (TraceCorQObject.importedRectangleCount_eq_certificateLedger_count
      triple.first.sourceObject)

/-- The right-associated target object imported count is counted by the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetImportedRectangleCount =
      triple.third.targetObject.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetImportedRectangleObjectCount
      triple)
    (TraceCorQObject.importedRectangleCount_eq_certificateLedger_count
      triple.third.targetObject)

/-- The left-associated source object bookkeeping count is counted by the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.sourceObject.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount
      triple)
    (TraceCorQObject.traceBookkeepingCount_eq_certificateLedger_count
      triple.first.sourceObject)

/-- The left-associated target object bookkeeping count is counted by the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.targetObject.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount
      triple)
    (TraceCorQObject.traceBookkeepingCount_eq_certificateLedger_count
      triple.third.targetObject)

/-- The right-associated source object bookkeeping count is counted by the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceTraceBookkeepingCount =
      triple.first.sourceObject.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceTraceBookkeepingObjectCount
      triple)
    (TraceCorQObject.traceBookkeepingCount_eq_certificateLedger_count
      triple.first.sourceObject)

/-- The right-associated target object bookkeeping count is counted by the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetTraceBookkeepingCount =
      triple.third.targetObject.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetTraceBookkeepingObjectCount
      triple)
    (TraceCorQObject.traceBookkeepingCount_eq_certificateLedger_count
      triple.third.targetObject)

/-- The left-associated source object rewrite-step count is counted by the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.sourceObject.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount
      triple)
    (TraceCorQObject.rewriteStepCount_eq_certificateLedger_count
      triple.first.sourceObject)

/-- The left-associated target object rewrite-step count is counted by the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.targetObject.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount
      triple)
    (TraceCorQObject.rewriteStepCount_eq_certificateLedger_count
      triple.third.targetObject)

/-- The right-associated source object rewrite-step count is counted by the first source ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.sourceRewriteStepCount =
      triple.first.sourceObject.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_sourceRewriteStepObjectCount
      triple)
    (TraceCorQObject.rewriteStepCount_eq_certificateLedger_count
      triple.first.sourceObject)

/-- The right-associated target object rewrite-step count is counted by the third target ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount_eq_certificateLedger_count
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedLocalizedForwardArrow.targetRewriteStepCount =
      triple.third.targetObject.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow_targetRewriteStepObjectCount
      triple)
    (TraceCorQObject.rewriteStepCount_eq_certificateLedger_count
      triple.third.targetObject)

end AnalyticMotives
end LFunctions
end Boundary
