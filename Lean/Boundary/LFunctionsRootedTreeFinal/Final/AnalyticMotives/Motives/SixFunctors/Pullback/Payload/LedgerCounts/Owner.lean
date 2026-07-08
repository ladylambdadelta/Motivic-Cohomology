import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Payload.Owner

/-!
# Ledger-count facts for compact-generator pullback payload

This file records that counts carried by the concrete compact-generator
pullback functional are counted by the certificate ledgers of the corresponding
evaluation endpoints.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source payload count is counted by the target generator ledger. -/
theorem TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount morphism =
      target.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger
    target

/-- Pullback target payload count is counted by the source generator ledger. -/
theorem TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount morphism =
      source.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger
    source

/-- Pullback source bookkeeping count is counted by the target generator ledger. -/
theorem TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount morphism =
      target.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.traceBookkeepingCount_eq_certificateLedger
    target

/-- Pullback target bookkeeping count is counted by the source generator ledger. -/
theorem TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount morphism =
      source.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.traceBookkeepingCount_eq_certificateLedger
    source

/-- Pullback source rewrite count is counted by the target generator ledger. -/
theorem TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.rewriteStepCount_eq_certificateLedger
    target

/-- Pullback target rewrite count is counted by the source generator ledger. -/
theorem TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount morphism =
      source.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.rewriteStepCount_eq_certificateLedger
    source

end AnalyticMotives
end LFunctions
end Boundary
