import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorPayload.Operations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorPayload.Payload.Owner

/-!
# Top-level compact-generator six-functor payload wrappers

This file mirrors the motive-root compact-generator pullback and pushforward
payload surface under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes pullback source imported rectangles. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles morphism =
      target.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceImportedRectangles_eq_target_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback target imported rectangles. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles morphism =
      source.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorPullback_targetImportedRectangles_eq_source_certificateLedger
    morphism

/-- The analytic-motives root exposes pushforward source imported rectangles. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforward_sourceImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles morphism =
      source.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorPushforward_sourceImportedRectangles_eq_source_certificateLedger
    morphism

/-- The analytic-motives root exposes pushforward target imported rectangles. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforward_targetImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles morphism =
      target.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorPushforward_targetImportedRectangles_eq_target_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback source bookkeeping payload. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount morphism =
      target.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceTraceBookkeepingCount_eq_target_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback target bookkeeping payload. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount morphism =
      source.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorPullback_targetTraceBookkeepingCount_eq_source_certificateLedger
    morphism

/-- The analytic-motives root exposes pushforward source bookkeeping payload. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforward_sourceTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount morphism =
      source.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorPushforward_sourceTraceBookkeepingCount_eq_source_certificateLedger
    morphism

/-- The analytic-motives root exposes pushforward target bookkeeping payload. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforward_targetTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount morphism =
      target.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorPushforward_targetTraceBookkeepingCount_eq_target_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback source rewrite-step payload. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceRewriteStepCount_eq_target_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback target rewrite-step payload. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount morphism =
      source.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorPullback_targetRewriteStepCount_eq_source_certificateLedger
    morphism

/-- The analytic-motives root exposes pushforward source rewrite-step payload. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforward_sourceRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount morphism =
      source.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorPushforward_sourceRewriteStepCount_eq_source_certificateLedger
    morphism

/-- The analytic-motives root exposes pushforward target rewrite-step payload. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforward_targetRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorPushforward_targetRewriteStepCount_eq_target_certificateLedger
    morphism

/-- The analytic-motives root exposes pullback source ledger rectangle lengths. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceCertificateLedgerRectangles_length
    morphism

/-- The analytic-motives root exposes pullback target ledger rectangle lengths. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGeneratorPullback_targetCertificateLedgerRectangles_length
    morphism

/-- The analytic-motives root exposes pushforward source ledger rectangle lengths. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforward_sourceCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGeneratorPushforward_sourceCertificateLedgerRectangles_length
    morphism

/-- The analytic-motives root exposes pushforward target ledger rectangle lengths. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforward_targetCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGeneratorPushforward_targetCertificateLedgerRectangles_length
    morphism

end AnalyticMotives
end LFunctions
end Boundary
