import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Payload.Owner

/-!
# Compact-generator six-functor payload wrappers

This file owns motive-root wrappers for the concrete payload carried by the
compact-generator pullback and pushforward functionals.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compact-generator pullback source imported rectangles are the target ledger rectangles. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles morphism =
      target.certificateLedger.importedRectangles :=
  TraceSixFunctor.compactGeneratorPullback_sourceImportedRectangles_eq_target_certificateLedger
    morphism

/-- Compact-generator pullback target imported rectangles are the source ledger rectangles. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles morphism =
      source.certificateLedger.importedRectangles :=
  TraceSixFunctor.compactGeneratorPullback_targetImportedRectangles_eq_source_certificateLedger
    morphism

/-- Compact-generator pushforward source imported rectangles are the source ledger rectangles. -/
theorem TraceAnalyticMotive.compactGeneratorPushforward_sourceImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles morphism =
      source.certificateLedger.importedRectangles :=
  TraceSixFunctor.compactGeneratorPushforward_sourceImportedRectangles_eq_source_certificateLedger
    morphism

/-- Compact-generator pushforward target imported rectangles are the target ledger rectangles. -/
theorem TraceAnalyticMotive.compactGeneratorPushforward_targetImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles morphism =
      target.certificateLedger.importedRectangles :=
  TraceSixFunctor.compactGeneratorPushforward_targetImportedRectangles_eq_target_certificateLedger
    morphism

/-- Compact-generator pullback source bookkeeping is counted by the target ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount morphism =
      target.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctor.compactGeneratorPullback_sourceTraceBookkeepingCount_eq_target_certificateLedger
    morphism

/-- Compact-generator pullback target bookkeeping is counted by the source ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount morphism =
      source.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctor.compactGeneratorPullback_targetTraceBookkeepingCount_eq_source_certificateLedger
    morphism

/-- Compact-generator pushforward source bookkeeping is counted by the source ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPushforward_sourceTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount morphism =
      source.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctor.compactGeneratorPushforward_sourceTraceBookkeepingCount_eq_source_certificateLedger
    morphism

/-- Compact-generator pushforward target bookkeeping is counted by the target ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPushforward_targetTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount morphism =
      target.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctor.compactGeneratorPushforward_targetTraceBookkeepingCount_eq_target_certificateLedger
    morphism

/-- Compact-generator pullback source rewrite steps are counted by the target ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceSixFunctor.compactGeneratorPullback_sourceRewriteStepCount_eq_target_certificateLedger
    morphism

/-- Compact-generator pullback target rewrite steps are counted by the source ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount morphism =
      source.certificateLedger.rewriteStepCount :=
  TraceSixFunctor.compactGeneratorPullback_targetRewriteStepCount_eq_source_certificateLedger
    morphism

/-- Compact-generator pushforward source rewrite steps are counted by the source ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPushforward_sourceRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount morphism =
      source.certificateLedger.rewriteStepCount :=
  TraceSixFunctor.compactGeneratorPushforward_sourceRewriteStepCount_eq_source_certificateLedger
    morphism

/-- Compact-generator pushforward target rewrite steps are counted by the target ledger. -/
theorem TraceAnalyticMotive.compactGeneratorPushforward_targetRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceSixFunctor.compactGeneratorPushforward_targetRewriteStepCount_eq_target_certificateLedger
    morphism

/-- Compact-generator pullback source ledger rectangle count is its target list length. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  TraceSixFunctor.compactGeneratorPullback_sourceCertificateLedgerRectangles_length
    morphism

/-- Compact-generator pullback target ledger rectangle count is its source list length. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  TraceSixFunctor.compactGeneratorPullback_targetCertificateLedgerRectangles_length
    morphism

/-- Compact-generator pushforward source ledger rectangle count is its source list length. -/
theorem TraceAnalyticMotive.compactGeneratorPushforward_sourceCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  TraceSixFunctor.compactGeneratorPushforward_sourceCertificateLedgerRectangles_length
    morphism

/-- Compact-generator pushforward target ledger rectangle count is its target list length. -/
theorem TraceAnalyticMotive.compactGeneratorPushforward_targetCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  TraceSixFunctor.compactGeneratorPushforward_targetCertificateLedgerRectangles_length
    morphism

end AnalyticMotives
end LFunctions
end Boundary
