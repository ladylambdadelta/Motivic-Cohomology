import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.LedgerCounts.Owner

/-!
# Motive-root compact morphism ledger counts

This file exposes endpoint certificate-ledger count facts for compact geometric
generator morphisms at the motive root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A compact-generator morphism source imported-rectangle count is the source ledger count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_sourceImportedRectangleCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangleCount =
      source.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_source_certificateLedger
    morphism

/-- A compact-generator morphism target imported-rectangle count is the target ledger count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_targetImportedRectangleCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangleCount =
      target.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_target_certificateLedger
    morphism

/-- A compact-generator morphism source bookkeeping count is the source ledger count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_sourceTraceBookkeepingCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceTraceBookkeepingCount =
      source.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.Hom.sourceTraceBookkeepingCount_eq_source_certificateLedger
    morphism

/-- A compact-generator morphism target bookkeeping count is the target ledger count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_targetTraceBookkeepingCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetTraceBookkeepingCount =
      target.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.Hom.targetTraceBookkeepingCount_eq_target_certificateLedger
    morphism

/-- A compact-generator morphism source rewrite-step count is the source ledger count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_sourceRewriteStepCount_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceRewriteStepCount =
      source.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.Hom.sourceRewriteStepCount_eq_source_certificateLedger
    morphism

/-- A compact-generator morphism target rewrite-step count is the target ledger count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_targetRewriteStepCount_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetRewriteStepCount =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.Hom.targetRewriteStepCount_eq_target_certificateLedger
    morphism

end AnalyticMotives
end LFunctions
end Boundary
