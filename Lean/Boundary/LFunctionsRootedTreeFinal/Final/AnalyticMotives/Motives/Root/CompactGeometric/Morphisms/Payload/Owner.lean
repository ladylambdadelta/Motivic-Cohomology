import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Morphisms.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Morphisms.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Morphisms.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Morphisms.Payload.Localized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Morphisms.Payload.Operations.Owner

/-!
# Motive-root compact morphism endpoint payloads

This file collects root facades for endpoint ledger rectangle and count facts
attached to compact geometric generator morphisms.  The aggregate surface
records source and target certificate-ledger payload recovery and composition
endpoint preservation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root aggregate compact morphism source rectangles come from the source ledger. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_payload_sourceImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangles =
      source.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorMorphism_sourceImportedRectangles_eq_source_certificateLedger
    morphism

/-- Motive-root aggregate compact morphism target rectangles come from the target ledger. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_payload_targetImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangles =
      target.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorMorphism_targetImportedRectangles_eq_target_certificateLedger
    morphism

/-- Motive-root aggregate compact morphism source imported-rectangle count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_payload_sourceImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangleCount =
      source.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_sourceImportedRectangleCount_eq_source_certificateLedger
    morphism

/-- Motive-root aggregate compact morphism target imported-rectangle count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_payload_targetImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangleCount =
      target.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_targetImportedRectangleCount_eq_target_certificateLedger
    morphism

/-- Motive-root aggregate compact morphism source bookkeeping count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_payload_sourceTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceTraceBookkeepingCount =
      source.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_sourceTraceBookkeepingCount_eq_source_certificateLedger
    morphism

/-- Motive-root aggregate compact morphism target rewrite-step count. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_payload_targetRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetRewriteStepCount =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorMorphism_targetRewriteStepCount_eq_target_certificateLedger
    morphism

/-- Motive-root aggregate compact morphism composition keeps the left source rectangles. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_payload_comp_sourceImportedRectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).sourceImportedRectangles =
      left.sourceImportedRectangles :=
  TraceAnalyticMotive.compactGeneratorMorphism_comp_sourceImportedRectangles
    left
    right

/-- Motive-root aggregate compact morphism composition keeps the right target rectangles. -/
theorem TraceAnalyticMotive.compactGeneratorMorphism_payload_comp_targetImportedRectangles
    {first second third : TraceAnalyticGeometricGenerator}
    (left : TraceAnalyticGeometricGenerator.Hom first second)
    (right : TraceAnalyticGeometricGenerator.Hom second third) :
    (TraceAnalyticGeometricGenerator.comp left right).targetImportedRectangles =
      right.targetImportedRectangles :=
  TraceAnalyticMotive.compactGeneratorMorphism_comp_targetImportedRectangles
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
