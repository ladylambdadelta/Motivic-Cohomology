import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Payload.Owner

/-!
# Ledger-count facts for compact-generator pushforward payload

This file records that counts carried by the concrete compact-generator
pushforward functional are counted by the certificate ledgers of the
corresponding source and target endpoints.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pushforward source payload count is counted by the source generator ledger. -/
theorem TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount morphism =
      source.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger
    source

/-- Pushforward target payload count is counted by the target generator ledger. -/
theorem TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount morphism =
      target.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger
    target

/-- Pushforward source bookkeeping count is counted by the source generator ledger. -/
theorem TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount morphism =
      source.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.traceBookkeepingCount_eq_certificateLedger
    source

/-- Pushforward target bookkeeping count is counted by the target generator ledger. -/
theorem TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount morphism =
      target.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.traceBookkeepingCount_eq_certificateLedger
    target

/-- Pushforward source rewrite count is counted by the source generator ledger. -/
theorem TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount morphism =
      source.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.rewriteStepCount_eq_certificateLedger
    source

/-- Pushforward target rewrite count is counted by the target generator ledger. -/
theorem TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.rewriteStepCount_eq_certificateLedger
    target

end AnalyticMotives
end LFunctions
end Boundary
