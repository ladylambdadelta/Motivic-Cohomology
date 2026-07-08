import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Pullback.Payload.LedgerRectangles.Owner

/-!
# Top-root compact pullback evaluation ledger rectangles

This file exposes certificate-ledger rectangle lists at compact pullback
evaluation endpoints.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source evaluation rectangles are the target certificate-ledger list. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_sourceEvaluationImportedRectangles_eq_target_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        morphism =
      target.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorPullback_sourceEvaluationImportedRectangles_eq_target_certificateLedger_root
    morphism

/-- Pullback target evaluation rectangles are the source certificate-ledger list. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_targetEvaluationImportedRectangles_eq_source_certificateLedger_root
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        morphism =
      source.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGeneratorPullback_targetEvaluationImportedRectangles_eq_source_certificateLedger_root
    morphism

end AnalyticMotives
end LFunctions
end Boundary
