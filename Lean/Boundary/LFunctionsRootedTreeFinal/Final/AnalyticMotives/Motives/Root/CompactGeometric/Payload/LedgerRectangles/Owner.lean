import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Payload.LedgerRectangles.Owner

/-!
# Motive-root compact generator localized ledger rectangles

This file exposes the certificate-ledger rectangle-list payload of the
localized object attached to a compact generator.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localized object rectangle list is the compact generator certificate-ledger list. -/
theorem TraceAnalyticMotive.compactGenerator_localizedObject_importedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.localizedObject_importedRectangles_eq_certificateLedger
    generator

end AnalyticMotives
end LFunctions
end Boundary
