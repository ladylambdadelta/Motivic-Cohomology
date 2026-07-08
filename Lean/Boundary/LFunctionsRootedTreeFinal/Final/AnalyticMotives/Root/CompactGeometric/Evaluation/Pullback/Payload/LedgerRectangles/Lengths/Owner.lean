import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Pullback.Payload.LedgerRectangles.Lengths.Owner

/-!
# Top-root compact pullback evaluation ledger rectangle lengths

This file exposes count-as-length facts for compact pullback evaluation endpoint
certificate-ledger rectangle lists.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source evaluation target ledger rectangle-list length has the source evaluation count. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluation_certificateLedgerRectangles_length_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluation_certificateLedgerRectangles_length_root
    morphism

/-- Pullback target evaluation source ledger rectangle-list length has the target evaluation count. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluation_certificateLedgerRectangles_length_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluation_certificateLedgerRectangles_length_root
    morphism

end AnalyticMotives
end LFunctions
end Boundary
