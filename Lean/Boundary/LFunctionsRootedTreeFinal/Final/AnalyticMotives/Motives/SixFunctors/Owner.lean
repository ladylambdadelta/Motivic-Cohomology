import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Naturality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Representable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Naturality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Representable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Yoneda.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Representable.Owner

/-!
# Compact-generator calculus functionals

This file owns the currently constructed analytic calculus functionals on
compact-generator motives: pullback by precomposition, pushforward by
postcomposition, their endpoint certificate payloads, and the representable
pullback-pushforward interaction law.

The exposed operations are the compact-generator pullback, pushforward, their
certificate-ledger accounting, and their representable naturality square.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The current compact-generator pullback functional is identity-functorial. -/
theorem TraceSixFunctor.compactGeneratorPullback_id
    (presheaf : TraceCorQPresheaf)
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGenerator
        presheaf
        (𝟙 generator) =
      𝟙 (generator.sections presheaf) :=
  TraceSixFunctorPullback.compactGenerator_id
    presheaf
    generator

/-- The current compact-generator pullback functional is contravariantly compositional. -/
theorem TraceSixFunctor.compactGeneratorPullback_comp
    (presheaf : TraceCorQPresheaf)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGenerator
        presheaf
        (left ≫ right) =
      TraceSixFunctorPullback.compactGenerator presheaf right ≫
        TraceSixFunctorPullback.compactGenerator presheaf left :=
  TraceSixFunctorPullback.compactGenerator_comp
    presheaf
    left
    right

/-- The current compact-generator pushforward functional is identity-functorial. -/
theorem TraceSixFunctor.compactGeneratorPushforward_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGenerator
        (𝟙 generator) =
      𝟙 generator.presheaf :=
  TraceSixFunctorPushforward.compactGenerator_id
    generator

/-- The current compact-generator pushforward functional is covariantly compositional. -/
theorem TraceSixFunctor.compactGeneratorPushforward_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGenerator
        (left ≫ right) =
      TraceSixFunctorPushforward.compactGenerator left ≫
        TraceSixFunctorPushforward.compactGenerator right :=
  TraceSixFunctorPushforward.compactGenerator_comp
    left
    right

/-- Pullback source bookkeeping payload is counted by the target generator ledger. -/
theorem TraceSixFunctor.compactGeneratorPullback_sourceTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount morphism =
      target.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullback.compactGeneratorSourceTraceBookkeepingCount_eq_target_certificateLedger
    morphism

/-- Pullback target bookkeeping payload is counted by the source generator ledger. -/
theorem TraceSixFunctor.compactGeneratorPullback_targetTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount morphism =
      source.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPullback.compactGeneratorTargetTraceBookkeepingCount_eq_source_certificateLedger
    morphism

/-- Pushforward source bookkeeping payload is counted by the source generator ledger. -/
theorem TraceSixFunctor.compactGeneratorPushforward_sourceTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount morphism =
      source.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPushforward.compactGeneratorSourceTraceBookkeepingCount_eq_source_certificateLedger
    morphism

/-- Pushforward target bookkeeping payload is counted by the target generator ledger. -/
theorem TraceSixFunctor.compactGeneratorPushforward_targetTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount morphism =
      target.certificateLedger.traceBookkeepingCount :=
  TraceSixFunctorPushforward.compactGeneratorTargetTraceBookkeepingCount_eq_target_certificateLedger
    morphism

/-- Pullback source rewrite-step payload is counted by the target generator ledger. -/
theorem TraceSixFunctor.compactGeneratorPullback_sourceRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullback.compactGeneratorSourceRewriteStepCount_eq_target_certificateLedger
    morphism

/-- Pullback target rewrite-step payload is counted by the source generator ledger. -/
theorem TraceSixFunctor.compactGeneratorPullback_targetRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount morphism =
      source.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPullback.compactGeneratorTargetRewriteStepCount_eq_source_certificateLedger
    morphism

/-- Pushforward source rewrite-step payload is counted by the source generator ledger. -/
theorem TraceSixFunctor.compactGeneratorPushforward_sourceRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount morphism =
      source.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPushforward.compactGeneratorSourceRewriteStepCount_eq_source_certificateLedger
    morphism

/-- Pushforward target rewrite-step payload is counted by the target generator ledger. -/
theorem TraceSixFunctor.compactGeneratorPushforward_targetRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceSixFunctorPushforward.compactGeneratorTargetRewriteStepCount_eq_target_certificateLedger
    morphism

/-- Pullback source imported rectangles are the target generator ledger rectangles. -/
theorem TraceSixFunctor.compactGeneratorPullback_sourceImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles morphism =
      target.certificateLedger.importedRectangles :=
  TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles_eq_target_certificateLedger
    morphism

/-- Pullback target imported rectangles are the source generator ledger rectangles. -/
theorem TraceSixFunctor.compactGeneratorPullback_targetImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles morphism =
      source.certificateLedger.importedRectangles :=
  TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles_eq_source_certificateLedger
    morphism

/-- Pushforward source imported rectangles are the source generator ledger rectangles. -/
theorem TraceSixFunctor.compactGeneratorPushforward_sourceImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles morphism =
      source.certificateLedger.importedRectangles :=
  TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles_eq_source_certificateLedger
    morphism

/-- Pushforward target imported rectangles are the target generator ledger rectangles. -/
theorem TraceSixFunctor.compactGeneratorPushforward_targetImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles morphism =
      target.certificateLedger.importedRectangles :=
  TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles_eq_target_certificateLedger
    morphism

/-- Pullback source ledger rectangle-list length is counted by the target ledger. -/
theorem TraceSixFunctor.compactGeneratorPullback_sourceCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  TraceSixFunctorPullback.compactGeneratorSource_certificateLedgerRectangles_length
    morphism

/-- Pullback target ledger rectangle-list length is counted by the source ledger. -/
theorem TraceSixFunctor.compactGeneratorPullback_targetCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  TraceSixFunctorPullback.compactGeneratorTarget_certificateLedgerRectangles_length
    morphism

/-- Pushforward source ledger rectangle-list length is counted by the source ledger. -/
theorem TraceSixFunctor.compactGeneratorPushforward_sourceCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  TraceSixFunctorPushforward.compactGeneratorSource_certificateLedgerRectangles_length
    morphism

/-- Pushforward target ledger rectangle-list length is counted by the target ledger. -/
theorem TraceSixFunctor.compactGeneratorPushforward_targetCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  TraceSixFunctorPushforward.compactGeneratorTarget_certificateLedgerRectangles_length
    morphism

/-- The current representable pullback and pushforward operators commute. -/
theorem TraceSixFunctor.compactGeneratorPullbackPushforward_representable_naturality
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        source
        probe ≫
        TraceSixFunctorPushforward.representablePostcompositionOperator
          probeSource
          morphism =
      TraceSixFunctorPushforward.representablePostcompositionOperator
          probeTarget
          morphism ≫
        TraceSixFunctorPullback.representablePrecompositionOperator
          target
          probe :=
  TraceSixFunctorPullbackPushforward.representableOperator_naturality
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
