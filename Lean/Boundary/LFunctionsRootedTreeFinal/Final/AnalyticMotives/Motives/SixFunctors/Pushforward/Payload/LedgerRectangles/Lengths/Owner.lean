import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Payload.LedgerRectangles.Owner

/-!
# Lengths of compact-generator pushforward ledger rectangle lists

This file connects compact-generator pushforward certificate-ledger
rectangle-list formulas to the corresponding certificate-ledger count formulas.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pushforward source ledger rectangle-list length is counted by the source generator ledger. -/
theorem TraceSixFunctorPushforward.compactGeneratorSource_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount_eq_source_certificateLedger
        morphism))
    (Eq.trans
      (TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount_eq_length
        morphism)
      (congrArg
        List.length
        (TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangles_eq_source_certificateLedger
          morphism)))

/-- Pushforward target ledger rectangle-list length is counted by the target generator ledger. -/
theorem TraceSixFunctorPushforward.compactGeneratorTarget_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount_eq_target_certificateLedger
        morphism))
    (Eq.trans
      (TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount_eq_length
        morphism)
      (congrArg
        List.length
        (TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangles_eq_target_certificateLedger
          morphism)))

end AnalyticMotives
end LFunctions
end Boundary
