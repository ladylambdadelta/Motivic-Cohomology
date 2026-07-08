import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Payload.Owner

/-!
# Ledger rectangle lists for compact-generator pushforward payload

This file records that imported-rectangle lists carried by compact-generator
pushforward are exactly the certificate-ledger rectangle lists of the
corresponding source and target endpoints.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pushforward source payload rectangles are the source generator ledger rectangles. -/
theorem TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles morphism =
      source.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
    source

/-- Pushforward target payload rectangles are the target generator ledger rectangles. -/
theorem TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles morphism =
      target.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
    target

end AnalyticMotives
end LFunctions
end Boundary
