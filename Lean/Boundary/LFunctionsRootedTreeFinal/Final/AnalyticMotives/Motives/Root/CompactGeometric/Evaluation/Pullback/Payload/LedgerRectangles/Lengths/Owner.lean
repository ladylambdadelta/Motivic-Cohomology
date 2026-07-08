import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Payload.LedgerRectangles.Lengths.Owner

/-!
# Motive-root compact pullback evaluation ledger rectangle lengths

This file exposes count-as-length facts for compact pullback evaluation endpoint
certificate-ledger rectangle lists.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source evaluation target ledger rectangle-list length has the source evaluation count. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluation_certificateLedgerRectangles_length_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.pullbackSourceEvaluation_certificateLedgerRectangles_length
    morphism

/-- Pullback target evaluation source ledger rectangle-list length has the target evaluation count. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_targetEvaluation_certificateLedgerRectangles_length_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.pullbackTargetEvaluation_certificateLedgerRectangles_length
    morphism

end AnalyticMotives
end LFunctions
end Boundary
