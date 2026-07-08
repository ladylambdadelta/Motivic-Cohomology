import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Payload.LedgerCounts.Owner

/-!
# Top-root compact generator localized ledger counts

This file exposes certificate-ledger count facts for the localized object
attached to a compact generator at the public root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localized object imported count is counted by the compact generator ledger. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedObject_importedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.importedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGenerator_localizedObject_importedRectangleCount_eq_certificateLedger
    generator

/-- The localized object bookkeeping count is counted by the compact generator ledger. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedObject_traceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.traceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGenerator_localizedObject_traceBookkeepingCount_eq_certificateLedger
    generator

/-- The localized object rewrite count is counted by the compact generator ledger. -/
theorem AnalyticMotivesRoot.compactGenerator_localizedObject_rewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.localizedObject.rewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGenerator_localizedObject_rewriteStepCount_eq_certificateLedger
    generator

end AnalyticMotives
end LFunctions
end Boundary
