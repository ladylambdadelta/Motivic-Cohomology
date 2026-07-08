import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Payload.LedgerRectangles.Owner

/-!
# Lengths of compact-generator pullback ledger rectangle lists

This file connects compact-generator pullback certificate-ledger rectangle-list
formulas to the corresponding certificate-ledger count formulas.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source ledger rectangle-list length is counted by the target generator ledger. -/
theorem TraceSixFunctorPullback.compactGeneratorSource_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount_eq_target_certificateLedger
        morphism))
    (Eq.trans
      (TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount_eq_length
        morphism)
      (congrArg
        List.length
        (TraceSixFunctorPullback.compactGeneratorSourceImportedRectangles_eq_target_certificateLedger
          morphism)))

/-- Pullback target ledger rectangle-list length is counted by the source generator ledger. -/
theorem TraceSixFunctorPullback.compactGeneratorTarget_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount_eq_source_certificateLedger
        morphism))
    (Eq.trans
      (TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount_eq_length
        morphism)
      (congrArg
        List.length
        (TraceSixFunctorPullback.compactGeneratorTargetImportedRectangles_eq_source_certificateLedger
          morphism)))

end AnalyticMotives
end LFunctions
end Boundary
