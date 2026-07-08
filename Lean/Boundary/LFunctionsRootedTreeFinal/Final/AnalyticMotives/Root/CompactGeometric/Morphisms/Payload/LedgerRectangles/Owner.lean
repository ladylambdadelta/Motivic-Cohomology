import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Morphisms.Payload.LedgerRectangles.Owner

/-!
# Top-root compact morphism ledger rectangles

This file exposes endpoint certificate-ledger rectangle facts for compact
geometric generator morphisms at the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A compact-generator morphism source rectangle list is the source certificate ledger list. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_sourceImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangles =
      source.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorMorphism_sourceImportedRectangles_eq_source_certificateLedger
    morphism

/-- A compact-generator morphism target rectangle list is the target certificate ledger list. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_targetImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangles =
      target.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorMorphism_targetImportedRectangles_eq_target_certificateLedger
    morphism

end AnalyticMotives
end LFunctions
end Boundary
