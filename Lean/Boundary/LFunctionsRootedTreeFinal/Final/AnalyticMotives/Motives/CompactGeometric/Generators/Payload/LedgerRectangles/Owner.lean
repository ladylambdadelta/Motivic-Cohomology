import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.ImportedRectangles.LedgerRectangles.Owner

/-!
# Ledger rectangle lists for compact-generator localized payloads

This file records that the imported-rectangle list carried by the localized
object attached to a compact generator is its certificate-ledger rectangle list.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localized object rectangle list is the compact generator certificate-ledger list. -/
theorem TraceAnalyticGeometricGenerator.localizedObject_importedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceLocalizedWordObject.importedRectangles_eq_certificateLedger_rectangles
    generator.localizedObject

end AnalyticMotives
end LFunctions
end Boundary
