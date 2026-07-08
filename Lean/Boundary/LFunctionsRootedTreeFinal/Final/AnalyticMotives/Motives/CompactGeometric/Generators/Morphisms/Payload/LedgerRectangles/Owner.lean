import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.Owner

/-!
# Ledger rectangle lists for compact-generator morphism payloads

This file records that the endpoint imported-rectangle lists carried by a
compact-generator morphism are exactly the certificate-ledger rectangle lists of
the corresponding source and target generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A compact morphism source endpoint rectangle list is the source certificate-ledger list. -/
theorem TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.sourceImportedRectangles =
      source.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
    source

/-- A compact morphism target endpoint rectangle list is the target certificate-ledger list. -/
theorem TraceAnalyticGeometricGenerator.Hom.targetImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    morphism.targetImportedRectangles =
      target.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
    target

end AnalyticMotives
end LFunctions
end Boundary
