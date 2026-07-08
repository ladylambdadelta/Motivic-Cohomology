import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Pullback.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Evaluation.Pullback.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Evaluation.Pullback.Payload.LedgerRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Evaluation.Pullback.Payload.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Evaluation.Pullback.Payload.Owner

/-!
# Top-root compact pullback evaluation

This file collects public root facades for compact-generator pullback
evaluation payloads.  The aggregate surface records how pullback evaluation
endpoints exchange the source and target payloads of a compact morphism.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root aggregate pullback source evaluation rectangles are the morphism target rectangles. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_evaluationSummary_sourceImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        morphism =
      morphism.targetImportedRectangles :=
  TraceAnalyticMotive.compactGeneratorPullback_evaluationSummary_sourceImportedRectangles
    morphism

/-- Top-root aggregate pullback target evaluation rectangles are the morphism source rectangles. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_evaluationSummary_targetImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        morphism =
      morphism.sourceImportedRectangles :=
  TraceAnalyticMotive.compactGeneratorPullback_evaluationSummary_targetImportedRectangles
    morphism

/-- Top-root aggregate pullback source evaluation count is the target ledger count. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_evaluationSummary_sourceImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangleCount
        morphism =
      target.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorPullback_evaluationSummary_sourceImportedRectangleCount
    morphism

/-- Top-root aggregate pullback target evaluation count is the source ledger count. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_evaluationSummary_targetImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangleCount
        morphism =
      source.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGeneratorPullback_evaluationSummary_targetImportedRectangleCount
    morphism

/-- Top-root aggregate pullback source evaluation rewrite count is the target ledger count. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_evaluationSummary_sourceRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationRewriteStepCount
        morphism =
      target.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGeneratorPullback_evaluationSummary_sourceRewriteStepCount
    morphism

/-- Top-root aggregate identity pullback has matching endpoint rectangle payloads. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_evaluationSummary_identityRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.pullbackSourceEvaluationImportedRectangles
        (𝟙 generator) =
      TraceAnalyticGeometricGenerator.pullbackTargetEvaluationImportedRectangles
        (𝟙 generator) :=
  TraceAnalyticMotive.compactGeneratorPullback_evaluationSummary_identityRectangles
    generator

end AnalyticMotives
end LFunctions
end Boundary
