import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Morphisms.Payload.LedgerRectangles.Lengths.Owner

/-!
# Top-root compact morphism ledger rectangle lengths

This file exposes endpoint certificate-ledger rectangle length facts for compact
geometric generator morphisms at the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source certificate-ledger rectangle list of a compact-generator morphism has the source count. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_source_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGeneratorMorphism_source_certificateLedgerRectangles_length
    morphism

/-- The target certificate-ledger rectangle list of a compact-generator morphism has the target count. -/
theorem AnalyticMotivesRoot.compactGeneratorMorphism_target_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGeneratorMorphism_target_certificateLedgerRectangles_length
    morphism

end AnalyticMotives
end LFunctions
end Boundary
