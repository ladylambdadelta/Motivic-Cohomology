import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ChannelRectangle.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ChannelRectangle.Functoriality.Owner

/-!
# Compact generator for the zero-pole scheduled-channel rectangle seed

This file lifts the scheduled-channel rectangle trace presentation from the
concrete completed-zeta finite-rectangle adapter into the compact geometric
analytic generator lane, and owns the explicit candidate and payload facts.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The explicit candidate representing the scheduled-channel compact-generator morphism. -/
def completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQQuotientCandidate :=
  completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate f F h u

/-- The compact-generator morphism has the pipeline candidate as explicit representative data. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHomCandidate_eq_pipeline
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelRectangleGeneratorHomCandidate f F h u =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate f F h u :=
  rfl

/-- The explicit scheduled-channel morphism candidate has the pipeline candidate certificate ledger. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHomCandidate_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
      f F h u).certificateLedger =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
        f F h u).certificateLedger :=
  rfl

/-- The explicit scheduled-channel candidate ledger is formal-sum certificates then relation certificates. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHomCandidate_certificateLedger_decomposition
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
      f F h u).certificateLedger =
      ResidueChannelCertificateLedger.append
        (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
          f F h u).formalSum.certificateLedger
        (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
          f F h u).ledger.certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate f F h u)

/-- The scheduled-channel source generator imports the pipeline source rectangle payload. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_importedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).importedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).importedRectangles :=
  rfl

/-- The scheduled-channel source generator has the pipeline source certificate ledger. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).certificateLedger =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).certificateLedger :=
  rfl

/-- The scheduled-channel source generator imports the pipeline source rectangle count. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).importedRectangleCount :=
  rfl

/-- The scheduled-channel source generator rectangle count is counted by its rectangle list. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_importedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).importedRectangles.length :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u)

/-- The scheduled-channel source generator keeps the pipeline source bookkeeping count. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).traceBookkeepingCount :=
  rfl

/-- The scheduled-channel source generator keeps the pipeline source rewrite-step count. -/
theorem completedZetaZeroPoleChannelRectangleSourceGenerator_rewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleSourceGenerator f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).rewriteStepCount :=
  rfl

/-- The scheduled-channel target generator imports the pipeline target rectangle payload. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_importedRectangles :
    completedZetaZeroPoleChannelRectangleTargetGenerator.importedRectangles =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangles :=
  rfl

/-- The scheduled-channel target generator has the pipeline target certificate ledger. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_certificateLedger :
    completedZetaZeroPoleChannelRectangleTargetGenerator.certificateLedger =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.certificateLedger :=
  rfl

/-- The scheduled-channel target generator imports the pipeline target rectangle count. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_importedRectangleCount :
    completedZetaZeroPoleChannelRectangleTargetGenerator.importedRectangleCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangleCount :=
  rfl

/-- The scheduled-channel target generator rectangle count is counted by its rectangle list. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_importedRectangleCount_eq_length :
    completedZetaZeroPoleChannelRectangleTargetGenerator.importedRectangleCount =
      completedZetaZeroPoleChannelRectangleTargetGenerator.importedRectangles.length :=
  TraceAnalyticGeometricGenerator.importedRectangleCount_eq_length_importedRectangles
    completedZetaZeroPoleChannelRectangleTargetGenerator

/-- The scheduled-channel target generator keeps the pipeline target bookkeeping count. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_traceBookkeepingCount :
    completedZetaZeroPoleChannelRectangleTargetGenerator.traceBookkeepingCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.traceBookkeepingCount :=
  rfl

/-- The scheduled-channel target generator keeps the pipeline target rewrite-step count. -/
theorem completedZetaZeroPoleChannelRectangleTargetGenerator_rewriteStepCount :
    completedZetaZeroPoleChannelRectangleTargetGenerator.rewriteStepCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.rewriteStepCount :=
  rfl

/-- The scheduled-channel compact morphism source endpoint has the source generator payload. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_sourceImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom
      f F h u).sourceImportedRectangles =
      (completedZetaZeroPoleChannelRectangleSourceGenerator
        f F h u).importedRectangles :=
  rfl

/-- The scheduled-channel compact morphism target endpoint has the target generator payload. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_targetImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom
      f F h u).targetImportedRectangles =
      completedZetaZeroPoleChannelRectangleTargetGenerator.importedRectangles :=
  rfl

/-- The scheduled-channel compact morphism source endpoint count is the source count. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_sourceImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom
      f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleSourceGenerator
        f F h u).importedRectangleCount :=
  rfl

/-- The scheduled-channel compact morphism target endpoint count is the target count. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_targetImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom
      f F h u).targetImportedRectangleCount =
      completedZetaZeroPoleChannelRectangleTargetGenerator.importedRectangleCount :=
  rfl

/-- The scheduled-channel compact morphism source endpoint count is counted by its rectangles. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_sourceImportedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom
      f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom
        f F h u).sourceImportedRectangles.length :=
  TraceAnalyticGeometricGenerator.Hom.sourceImportedRectangleCount_eq_length
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u)

/-- The scheduled-channel compact morphism target endpoint count is counted by its rectangles. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_targetImportedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom
      f F h u).targetImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom
        f F h u).targetImportedRectangles.length :=
  TraceAnalyticGeometricGenerator.Hom.targetImportedRectangleCount_eq_length
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u)

/-- The scheduled-channel compact morphism source endpoint bookkeeping count is the source count. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_sourceTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom
      f F h u).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleChannelRectangleSourceGenerator
        f F h u).traceBookkeepingCount :=
  rfl

/-- The scheduled-channel compact morphism target endpoint bookkeeping count is the target count. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_targetTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom
      f F h u).targetTraceBookkeepingCount =
      completedZetaZeroPoleChannelRectangleTargetGenerator.traceBookkeepingCount :=
  rfl

/-- The scheduled-channel compact morphism source endpoint rewrite count is the source count. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_sourceRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom
      f F h u).sourceRewriteStepCount =
      (completedZetaZeroPoleChannelRectangleSourceGenerator
        f F h u).rewriteStepCount :=
  rfl

/-- The scheduled-channel compact morphism target endpoint rewrite count is the target count. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_targetRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom
      f F h u).targetRewriteStepCount =
      completedZetaZeroPoleChannelRectangleTargetGenerator.rewriteStepCount :=
  rfl

/-- The explicit scheduled-channel morphism candidate imports the pipeline candidate rectangle list. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHomCandidate_importedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
      f F h u).importedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
        f F h u).importedRectangles :=
  rfl

/-- The explicit scheduled-channel morphism candidate imports the pipeline candidate rectangle count. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHomCandidate_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
        f F h u).importedRectangleCount :=
  rfl

/-- The explicit scheduled-channel candidate rectangle count is counted by its rectangle list. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHomCandidate_importedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
        f F h u).importedRectangles.length :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate f F h u)

/-- The explicit scheduled-channel morphism candidate keeps the pipeline candidate bookkeeping count. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHomCandidate_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
        f F h u).traceBookkeepingCount :=
  rfl

/-- The explicit scheduled-channel morphism candidate keeps the pipeline candidate rewrite-step count. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHomCandidate_rewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
        f F h u).rewriteStepCount :=
  rfl

/-- The explicit scheduled-channel candidate imports formal-sum payload and empty ledger payload. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHomCandidate_importedRectangleCount_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).importedRectangleCount +
        TraceCorQRelationLedger.empty.importedRectangleCount :=
  completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_importedRectangleCount_split
    f F h u

/-- The explicit scheduled-channel candidate exposes formal-sum rectangles and empty ledger rectangles. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHomCandidate_importedRectangles_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
      f F h u).importedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).importedRectangles ++
        TraceCorQRelationLedger.empty.importedRectangles :=
  completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_importedRectangles_split
    f F h u

/-- The explicit scheduled-channel candidate keeps formal-sum bookkeeping and empty ledger bookkeeping. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHomCandidate_traceBookkeepingCount_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).traceBookkeepingCount +
        TraceCorQRelationLedger.empty.traceBookkeepingCount :=
  completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_traceBookkeepingCount_split
    f F h u

/-- The explicit scheduled-channel candidate keeps formal-sum rewrite steps and empty ledger steps. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHomCandidate_rewriteStepCount_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHomCandidate
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).rewriteStepCount +
        TraceCorQRelationLedger.empty.rewriteStepCount :=
  completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_rewriteStepCount_split
    f F h u

/-- The scheduled-channel compact morphism is sound at its schedule parameter. -/
theorem completedZetaZeroPoleChannelRectangleGeneratorHom_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaZeroPoleChannelScheduledRectanglePipeline_sound
    f F h u

end AnalyticMotives
end LFunctions
end Boundary
