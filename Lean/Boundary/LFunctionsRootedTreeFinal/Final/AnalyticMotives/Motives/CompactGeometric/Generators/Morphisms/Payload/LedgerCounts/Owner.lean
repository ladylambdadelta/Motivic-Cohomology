import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.Owner

/-!
# Ledger counts for compact-generator morphism payloads

This file records that endpoint counts carried by compact-generator morphisms
are counted by the certificate ledgers of the corresponding source and target
generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A compact morphism source imported-rectangle count is counted by the source ledger. -/
theorem TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangleCount =
      source.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger
    source

/-- A compact morphism target imported-rectangle count is counted by the target ledger. -/
theorem TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangleCount =
      target.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger
    target

/-- A compact morphism source bookkeeping count is counted by the source ledger. -/
theorem TraceAnalyticGeometricGenerator.Hom.sourceTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceTraceBookkeepingCount =
      source.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.traceBookkeepingCount_eq_certificateLedger
    source

/-- A compact morphism target bookkeeping count is counted by the target ledger. -/
theorem TraceAnalyticGeometricGenerator.Hom.targetTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetTraceBookkeepingCount =
      target.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.traceBookkeepingCount_eq_certificateLedger
    target

/-- A compact morphism source rewrite count is counted by the source ledger. -/
theorem TraceAnalyticGeometricGenerator.Hom.sourceRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceRewriteStepCount =
      source.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.rewriteStepCount_eq_certificateLedger
    source

/-- A compact morphism target rewrite count is counted by the target ledger. -/
theorem TraceAnalyticGeometricGenerator.Hom.targetRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetRewriteStepCount =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.rewriteStepCount_eq_certificateLedger
    target

end AnalyticMotives
end LFunctions
end Boundary
