import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Ledger counts for compact-generator localized payloads

This file records that counts carried by the localized-word object attached to
a compact generator are counted by the compact generator's certificate ledger.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localized object imported count is counted by the compact generator ledger. -/
theorem TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount
      generator)
    (TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger
      generator)

/-- The localized object bookkeeping count is counted by the compact generator ledger. -/
theorem TraceAnalyticGeometricGenerator.localizedObject_traceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.traceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceLocalizedWordObject.traceBookkeepingCount_eq_certificateLedger_count
    generator.localizedObject

/-- The localized object rewrite count is counted by the compact generator ledger. -/
theorem TraceAnalyticGeometricGenerator.localizedObject_rewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.rewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceLocalizedWordObject.rewriteStepCount_eq_certificateLedger_count
    generator.localizedObject

end AnalyticMotives
end LFunctions
end Boundary
