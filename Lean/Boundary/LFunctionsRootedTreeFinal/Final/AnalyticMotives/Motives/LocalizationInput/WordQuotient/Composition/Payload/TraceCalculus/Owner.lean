import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Composition.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.TraceCalculus.ImportedRectangles.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Trace-calculus payload for composed localization word classes

This file records how endpoint certificate ledgers, trace-bookkeeping counts,
and rewrite-step counts behave under composition of localized word classes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composition keeps the left word class source endpoint certificate ledger. -/
theorem TraceLocalizationWordClass.comp_sourceCertificateLedger
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).sourceCertificateLedger =
      left.sourceCertificateLedger :=
  rfl

/-- Composition keeps the right word class target endpoint certificate ledger. -/
theorem TraceLocalizationWordClass.comp_targetCertificateLedger
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).targetCertificateLedger =
      right.targetCertificateLedger :=
  rfl

/-- Composition keeps the left word class source endpoint bookkeeping count. -/
theorem TraceLocalizationWordClass.comp_sourceTraceBookkeepingCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).sourceTraceBookkeepingCount =
      left.sourceTraceBookkeepingCount :=
  rfl

/-- Composition keeps the right word class target endpoint bookkeeping count. -/
theorem TraceLocalizationWordClass.comp_targetTraceBookkeepingCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).targetTraceBookkeepingCount =
      right.targetTraceBookkeepingCount :=
  rfl

/-- Composition keeps the left word class source endpoint rewrite-step count. -/
theorem TraceLocalizationWordClass.comp_sourceRewriteStepCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).sourceRewriteStepCount =
      left.sourceRewriteStepCount :=
  rfl

/-- Composition keeps the right word class target endpoint rewrite-step count. -/
theorem TraceLocalizationWordClass.comp_targetRewriteStepCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).targetRewriteStepCount =
      right.targetRewriteStepCount :=
  rfl

/-- The composed source imported rectangles are extracted from the composed source ledger. -/
theorem TraceLocalizationWordClass.comp_sourceImportedRectangles_eq_certificateLedger_rectangles
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).sourceImportedRectangles =
      (TraceLocalizationWordClass.comp left right).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationWordClass.sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationWordClass.comp left right)

/-- The composed target imported rectangles are extracted from the composed target ledger. -/
theorem TraceLocalizationWordClass.comp_targetImportedRectangles_eq_certificateLedger_rectangles
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).targetImportedRectangles =
      (TraceLocalizationWordClass.comp left right).targetCertificateLedger.importedRectangles :=
  TraceLocalizationWordClass.targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationWordClass.comp left right)

/-- The composed source imported count is counted by the composed source ledger. -/
theorem TraceLocalizationWordClass.comp_sourceImportedRectangleCount_eq_certificateLedger_count
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).sourceImportedRectangleCount =
      (TraceLocalizationWordClass.comp left right).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationWordClass.sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationWordClass.comp left right)

/-- The composed target imported count is counted by the composed target ledger. -/
theorem TraceLocalizationWordClass.comp_targetImportedRectangleCount_eq_certificateLedger_count
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).targetImportedRectangleCount =
      (TraceLocalizationWordClass.comp left right).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationWordClass.targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationWordClass.comp left right)

/-- The composed endpoint imported rectangles are extracted from the composed endpoint ledger. -/
theorem TraceLocalizationWordClass.comp_endpointImportedRectangles_eq_certificateLedger_rectangles
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).endpointImportedRectangles =
      (TraceLocalizationWordClass.comp left right).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationWordClass.endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationWordClass.comp left right)

/-- The composed endpoint imported count is counted by the composed endpoint ledger. -/
theorem TraceLocalizationWordClass.comp_endpointImportedRectangleCount_eq_certificateLedger_count
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp left right).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationWordClass.endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationWordClass.comp left right)

/-- The composed source bookkeeping count is counted by the composed source ledger. -/
theorem TraceLocalizationWordClass.comp_sourceTraceBookkeepingCount_eq_certificateLedger_count
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp left right).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationWordClass.sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationWordClass.comp left right)

/-- The composed target bookkeeping count is counted by the composed target ledger. -/
theorem TraceLocalizationWordClass.comp_targetTraceBookkeepingCount_eq_certificateLedger_count
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp left right).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationWordClass.targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationWordClass.comp left right)

/-- The composed source rewrite count is counted by the composed source ledger. -/
theorem TraceLocalizationWordClass.comp_sourceRewriteStepCount_eq_certificateLedger_count
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp left right).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationWordClass.sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationWordClass.comp left right)

/-- The composed target rewrite count is counted by the composed target ledger. -/
theorem TraceLocalizationWordClass.comp_targetRewriteStepCount_eq_certificateLedger_count
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWordClass first second)
    (right : TraceLocalizationWordClass second third) :
    (TraceLocalizationWordClass.comp left right).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp left right).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationWordClass.targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationWordClass.comp left right)

end AnalyticMotives
end LFunctions
end Boundary
