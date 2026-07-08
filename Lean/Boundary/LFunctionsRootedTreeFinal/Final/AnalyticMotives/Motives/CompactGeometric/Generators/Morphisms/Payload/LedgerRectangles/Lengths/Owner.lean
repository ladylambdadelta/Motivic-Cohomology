import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.LedgerRectangles.Owner

/-!
# Lengths of compact-generator morphism ledger rectangle lists

This file connects endpoint certificate-ledger rectangle-list formulas for
compact-generator morphisms to their endpoint imported-rectangle count formulas.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A compact morphism source certificate-ledger rectangle list has the source ledger count. -/
theorem TraceAnalyticGeometricGenerator.Hom.source_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger
        source))
    (Eq.trans
      (TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_length
        morphism)
      (congrArg
        List.length
        (TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangles_eq_source_certificateLedger
          morphism)))

/-- A compact morphism target certificate-ledger rectangle list has the target ledger count. -/
theorem TraceAnalyticGeometricGenerator.Hom.target_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : TraceAnalyticGeometricGenerator.Hom source target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger
        target))
    (Eq.trans
      (TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_length
        morphism)
      (congrArg
        List.length
        (TraceAnalyticGeometricGenerator.Hom.targetImportedRectangles_eq_target_certificateLedger
          morphism)))

end AnalyticMotives
end LFunctions
end Boundary
