import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Payload.LedgerRectangles.Owner

/-!
# Lengths of compact-generator pullback evaluation ledger rectangle lists

This file connects pullback evaluation endpoint certificate-ledger
rectangle-list formulas to the corresponding endpoint imported-rectangle
count formulas.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source evaluation target ledger rectangle-list length has the source evaluation count. -/
theorem TraceAnalyticGeometricGenerator.pullbackSourceEvaluation_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.certificateLedger.importedRectangleCount =
      target.certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount_eq_target_certificateLedger
        morphism))
    (Eq.trans
      (TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount_eq_length
        morphism)
      (congrArg
        List.length
        (TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles_eq_target_certificateLedger
          morphism)))

/-- Pullback target evaluation source ledger rectangle-list length has the target evaluation count. -/
theorem TraceAnalyticGeometricGenerator.pullbackTargetEvaluation_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    source.certificateLedger.importedRectangleCount =
      source.certificateLedger.importedRectangles.length :=
  Eq.trans
    (Eq.sym
      (TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount_eq_source_certificateLedger
        morphism))
    (Eq.trans
      (TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount_eq_length
        morphism)
      (congrArg
        List.length
        (TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles_eq_source_certificateLedger
          morphism)))

end AnalyticMotives
end LFunctions
end Boundary
