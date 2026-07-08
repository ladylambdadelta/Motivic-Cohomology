import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ResidueRectangle.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ResidueRectangle.Functoriality.Owner

/-!
# Compact generator for the zero-pole residue rectangle seed

This file lifts the rectangle-certified zero-pole residue trace presentation
from the concrete completed-zeta finite-rectangle adapter into the compact
geometric analytic generator lane.  Functorial representable/Yoneda and
six-functor facts are owned by the `Functoriality` child.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The explicit candidate representing the residue rectangle compact-generator morphism. -/
def completedZetaZeroPoleResidueRectangleGeneratorHomCandidate
    (R : ℝ) :
    TraceCorQQuotientCandidate :=
  completedZetaZeroPoleResidueRectanglePipeline_candidate R

/-- The compact-generator morphism has the pipeline candidate as explicit representative data. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHomCandidate_eq_pipeline
    (R : ℝ) :
    completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R =
      completedZetaZeroPoleResidueRectanglePipeline_candidate R :=
  rfl

/-- The explicit residue rectangle morphism candidate has the pipeline candidate certificate ledger. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHomCandidate_certificateLedger
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).certificateLedger =
      (completedZetaZeroPoleResidueRectanglePipeline_candidate R).certificateLedger :=
  rfl

/-- The explicit residue rectangle candidate ledger is formal-sum certificates then relation certificates. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHomCandidate_certificateLedger_decomposition
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).certificateLedger =
      ResidueChannelCertificateLedger.append
        (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).formalSum.certificateLedger
        (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).ledger.certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R)

/-- The residue rectangle source generator imports the pipeline source rectangle payload. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_importedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangles :=
  rfl

/-- The residue rectangle source generator has the pipeline source certificate ledger. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_certificateLedger
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).certificateLedger =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).certificateLedger :=
  rfl

/-- The residue rectangle source generator imports the pipeline source rectangle count. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_importedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount :=
  rfl

/-- The residue rectangle source generator rectangle count is counted by its rectangle list. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangles.length :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleResidueRectangleSourceGenerator R)

/-- The residue rectangle source generator keeps the pipeline source bookkeeping count. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).traceBookkeepingCount :=
  rfl

/-- The residue rectangle source generator keeps the pipeline source rewrite-step count. -/
theorem completedZetaZeroPoleResidueRectangleSourceGenerator_rewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleSourceGenerator R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).rewriteStepCount :=
  rfl

/-- The residue rectangle target generator imports the pipeline target rectangle payload. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_importedRectangles :
    completedZetaZeroPoleResidueRectangleTargetGenerator.importedRectangles =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangles :=
  rfl

/-- The residue rectangle target generator has the pipeline target certificate ledger. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_certificateLedger :
    completedZetaZeroPoleResidueRectangleTargetGenerator.certificateLedger =
      completedZetaZeroPoleResidueRectanglePipeline_target.certificateLedger :=
  rfl

/-- The residue rectangle target generator imports the pipeline target rectangle count. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_importedRectangleCount :
    completedZetaZeroPoleResidueRectangleTargetGenerator.importedRectangleCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangleCount :=
  rfl

/-- The residue rectangle target generator rectangle count is counted by its rectangle list. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_importedRectangleCount_eq_length :
    completedZetaZeroPoleResidueRectangleTargetGenerator.importedRectangleCount =
      completedZetaZeroPoleResidueRectangleTargetGenerator.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_length_importedRectangles
    completedZetaZeroPoleResidueRectangleTargetGenerator

/-- The residue rectangle target generator keeps the pipeline target bookkeeping count. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_traceBookkeepingCount :
    completedZetaZeroPoleResidueRectangleTargetGenerator.traceBookkeepingCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.traceBookkeepingCount :=
  rfl

/-- The residue rectangle target generator keeps the pipeline target rewrite-step count. -/
theorem completedZetaZeroPoleResidueRectangleTargetGenerator_rewriteStepCount :
    completedZetaZeroPoleResidueRectangleTargetGenerator.rewriteStepCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.rewriteStepCount :=
  rfl

/-- The residue rectangle compact morphism source endpoint has the source generator payload. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_sourceImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles =
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangles :=
  rfl

/-- The residue rectangle compact morphism target endpoint has the target generator payload. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_targetImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles =
      completedZetaZeroPoleResidueRectangleTargetGenerator.importedRectangles :=
  rfl

/-- The residue rectangle compact morphism source endpoint count is the source count. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_sourceImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).importedRectangleCount :=
  rfl

/-- The residue rectangle compact morphism target endpoint count is the target count. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_targetImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      completedZetaZeroPoleResidueRectangleTargetGenerator.importedRectangleCount :=
  rfl

/-- The residue rectangle compact morphism source endpoint count is counted by its rectangles. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_sourceImportedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles.length :=
  TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_length
    (completedZetaZeroPoleResidueRectangleGeneratorHom R)

/-- The residue rectangle compact morphism target endpoint count is counted by its rectangles. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_targetImportedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles.length :=
  TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_length
    (completedZetaZeroPoleResidueRectangleGeneratorHom R)

/-- The residue rectangle compact morphism source endpoint bookkeeping count is the source count. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_sourceTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).traceBookkeepingCount :=
  rfl

/-- The residue rectangle compact morphism target endpoint bookkeeping count is the target count. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_targetTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetTraceBookkeepingCount =
      completedZetaZeroPoleResidueRectangleTargetGenerator.traceBookkeepingCount :=
  rfl

/-- The residue rectangle compact morphism source endpoint rewrite count is the source count. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_sourceRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceRewriteStepCount =
      (completedZetaZeroPoleResidueRectangleSourceGenerator R).rewriteStepCount :=
  rfl

/-- The residue rectangle compact morphism target endpoint rewrite count is the target count. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_targetRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetRewriteStepCount =
      completedZetaZeroPoleResidueRectangleTargetGenerator.rewriteStepCount :=
  rfl

/-- The explicit residue rectangle morphism candidate imports the pipeline candidate rectangle list. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHomCandidate_importedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).importedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_candidate R).importedRectangles :=
  rfl

/-- The explicit residue rectangle morphism candidate imports the pipeline candidate rectangle count. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHomCandidate_importedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_candidate R).importedRectangleCount :=
  rfl

/-- The explicit residue rectangle candidate rectangle count is counted by its rectangle list. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHomCandidate_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).importedRectangles.length :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R)

/-- The explicit residue rectangle morphism candidate keeps the pipeline candidate bookkeeping count. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHomCandidate_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_candidate R).traceBookkeepingCount :=
  rfl

/-- The explicit residue rectangle morphism candidate keeps the pipeline candidate rewrite-step count. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHomCandidate_rewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_candidate R).rewriteStepCount :=
  rfl

/-- The explicit residue rectangle candidate imports formal-sum payload and empty ledger payload. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHomCandidate_importedRectangleCount_split
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangleCount +
        TraceCorQRelationLedger.empty.importedRectangleCount :=
  completedZetaZeroPoleResidueRectanglePipeline_candidate_importedRectangleCount_split R

/-- The explicit residue rectangle candidate exposes formal-sum rectangles and empty ledger rectangles. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHomCandidate_importedRectangles_split
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).importedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangles ++
        TraceCorQRelationLedger.empty.importedRectangles :=
  completedZetaZeroPoleResidueRectanglePipeline_candidate_importedRectangles_split R

/-- The explicit residue rectangle candidate keeps formal-sum bookkeeping and empty ledger bookkeeping. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHomCandidate_traceBookkeepingCount_split
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).traceBookkeepingCount +
        TraceCorQRelationLedger.empty.traceBookkeepingCount :=
  completedZetaZeroPoleResidueRectanglePipeline_candidate_traceBookkeepingCount_split R

/-- The explicit residue rectangle candidate keeps formal-sum rewrite steps and empty ledger steps. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHomCandidate_rewriteStepCount_split
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHomCandidate R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).rewriteStepCount +
        TraceCorQRelationLedger.empty.rewriteStepCount :=
  completedZetaZeroPoleResidueRectanglePipeline_candidate_rewriteStepCount_split R

/-- The residue rectangle compact morphism is sound for positive finite-square height. -/
theorem completedZetaZeroPoleResidueRectangleGeneratorHom_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleResidueRectanglePipeline_sound
    f hPhi hR

end AnalyticMotives
end LFunctions
end Boundary
