import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Payload.LedgerRectangles.Lengths.Owner

/-!
# Motive-root compact generator localized ledger rectangle lengths

This file exposes the count-as-length fact for localized-object
certificate-ledger rectangle lists attached to compact generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localized object certificate-ledger rectangle list has the localized imported count. -/
theorem TraceAnalyticMotive.compactGenerator_localizedObject_certificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.certificateLedger.importedRectangleCount =
      generator.certificateLedger.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.localizedObject_certificateLedgerRectangles_length
    generator

end AnalyticMotives
end LFunctions
end Boundary
