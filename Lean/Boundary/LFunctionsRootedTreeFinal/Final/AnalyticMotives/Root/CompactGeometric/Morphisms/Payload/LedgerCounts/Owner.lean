import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Morphisms.Payload.LedgerCounts.Owner

/-!
# Top-root compact morphism ledger counts

This file exposes endpoint certificate-ledger count facts for compact geometric
generator morphisms at the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A compact-generator morphism source imported-rectangle count is the source ledger count. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_sourceImportedRectangleCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangleCount =
      source.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_sourceImportedRectangleCount_eq_source_certificateLedger
    morphism

/-- A compact-generator morphism target imported-rectangle count is the target ledger count. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_targetImportedRectangleCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangleCount =
      target.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_targetImportedRectangleCount_eq_target_certificateLedger
    morphism

/-- A compact-generator morphism source bookkeeping count is the source ledger count. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_sourceTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceTraceBookkeepingCount =
      source.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_sourceTraceBookkeepingCount_eq_source_certificateLedger
    morphism

/-- A compact-generator morphism target bookkeeping count is the target ledger count. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_targetTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetTraceBookkeepingCount =
      target.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_targetTraceBookkeepingCount_eq_target_certificateLedger
    morphism

/-- A compact-generator morphism source rewrite-step count is the source ledger count. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_sourceRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceRewriteStepCount =
      source.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_sourceRewriteStepCount_eq_source_certificateLedger
    morphism

/-- A compact-generator morphism target rewrite-step count is the target ledger count. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_targetRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetRewriteStepCount =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_targetRewriteStepCount_eq_target_certificateLedger
    morphism

end AnalyticMotives
end LFunctions
end Boundary
