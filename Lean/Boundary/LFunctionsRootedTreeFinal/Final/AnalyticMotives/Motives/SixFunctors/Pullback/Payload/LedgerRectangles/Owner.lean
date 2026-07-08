import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Payload.Owner

/-!
# Ledger rectangle lists for compact-generator pullback payload

This file records that imported-rectangle lists carried by compact-generator
pullback are exactly the certificate-ledger rectangle lists of the corresponding
evaluation endpoints.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source payload rectangles are the target generator ledger rectangles. -/
theorem TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles morphism =
      target.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles_eq_morphism_target
      morphism)
    (TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
      target)

/-- Pullback target payload rectangles are the source generator ledger rectangles. -/
theorem TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles morphism =
      source.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles_eq_morphism_source
      morphism)
    (TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
      source)

end AnalyticMotives
end LFunctions
end Boundary
