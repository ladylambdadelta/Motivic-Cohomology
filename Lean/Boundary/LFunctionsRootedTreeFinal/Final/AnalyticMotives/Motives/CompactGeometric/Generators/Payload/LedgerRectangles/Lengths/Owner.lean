import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Payload.LedgerRectangles.Owner

/-!
# Lengths of compact-generator localized ledger rectangle lists

This file connects localized-object certificate-ledger rectangle-list formulas
to localized-object imported-rectangle count formulas for compact generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The localized object certificate-ledger rectangle list has the localized imported count. -/
theorem TraceAnalyticGeometricGenerator.localizedObject_certificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.certificateLedger.importedRectangleCount =
      generator.certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount_eq_certificateLedger
        generator))
    (Eq.trans
      (TraceAnalyticGeometricGenerator.localizedObject_importedRectangleCount_eq_length
        generator)
      (congrArg
        List.length
        (TraceAnalyticGeometricGenerator.localizedObject_importedRectangles_eq_certificateLedger
          generator)))

end AnalyticMotives
end LFunctions
end Boundary
