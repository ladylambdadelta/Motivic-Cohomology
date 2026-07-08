import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Morphisms.Payload.LedgerRectangles.Owner

/-!
# Ledger rectangle lists for compact-generator pullback evaluation payloads

This file records that pullback source and target evaluation endpoint payloads
are exactly the corresponding target and source certificate-ledger rectangle
lists.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pullback source evaluation rectangles are the target certificate-ledger list. -/
theorem TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles_eq_target_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        morphism =
      target.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles_eq_morphism_target
      morphism)
    (TraceAnalyticGeometricGenerator.Hom.targetImportedRectangles_eq_target_certificateLedger
      morphism)

/-- Pullback target evaluation rectangles are the source certificate-ledger list. -/
theorem TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles_eq_source_certificateLedger
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        morphism =
      source.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles_eq_morphism_source
      morphism)
    (TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangles_eq_source_certificateLedger
      morphism)

end AnalyticMotives
end LFunctions
end Boundary
