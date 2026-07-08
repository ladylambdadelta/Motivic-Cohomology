import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Payload.LedgerRectangles.Lengths.Owner

/-!
# Top-root compact generator localized ledger rectangle lengths

This file exposes the count-as-length fact for localized-object
certificate-ledger rectangle lists attached to compact generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localized object certificate-ledger rectangle list has the localized imported count. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedObject_certificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.certificateLedger.importedRectangleCount =
      generator.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGenerator_localizedObject_certificateLedgerRectangles_length
    generator

end AnalyticMotives
end LFunctions
end Boundary
