import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Payload.LedgerRectangles.Owner

/-!
# Top-root compact generator localized ledger rectangles

This file exposes the certificate-ledger rectangle-list payload of the
localized object attached to a compact generator at the public root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localized object rectangle list is the compact generator certificate-ledger list. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedObject_importedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_localizedObject_importedRectangles_eq_certificateLedger
    generator

end AnalyticMotives
end LFunctions
end Boundary
