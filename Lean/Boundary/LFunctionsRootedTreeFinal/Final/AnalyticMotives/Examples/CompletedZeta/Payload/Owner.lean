import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Payload.Owner

/-!
# Completed-zeta example payload

This file exposes the completed-zeta compact morphism endpoint payload facts at
the example layer.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The residue rectangle example morphism source endpoint carries the source rectangles. -/
theorem completedZetaExample_residueRectangleHom_sourceImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangles :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_homSourceImportedRectangles
    R

/-- The residue rectangle example morphism target endpoint carries the target rectangles. -/
theorem completedZetaExample_residueRectangleHom_targetImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangles :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_homTargetImportedRectangles
    R

/-- The residue rectangle example morphism source endpoint carries the source rectangle count. -/
theorem completedZetaExample_residueRectangleHom_sourceImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_homSourceImportedRectangleCount
    R

/-- The residue rectangle example morphism target endpoint carries the target rectangle count. -/
theorem completedZetaExample_residueRectangleHom_targetImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangleCount :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_homTargetImportedRectangleCount
    R

/-- The residue rectangle example morphism target imports exactly its listed rectangles. -/
theorem completedZetaExample_residueRectangleHom_targetImportedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles.length :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_homTargetRectangleCount_eq_length
    R

/-- The residue rectangle example morphism source endpoint carries trace bookkeeping. -/
theorem completedZetaExample_residueRectangleHom_sourceTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).traceBookkeepingCount :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_homSourceTraceBookkeepingCount
    R

/-- The residue rectangle example morphism target endpoint carries trace bookkeeping. -/
theorem completedZetaExample_residueRectangleHom_targetTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetTraceBookkeepingCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.traceBookkeepingCount :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_homTargetTraceBookkeepingCount
    R

/-- The residue rectangle example morphism source endpoint carries rewrite-step count. -/
theorem completedZetaExample_residueRectangleHom_sourceRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceRewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).rewriteStepCount :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_homSourceRewriteStepCount
    R

/-- The residue rectangle example morphism target endpoint carries rewrite-step count. -/
theorem completedZetaExample_residueRectangleHom_targetRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetRewriteStepCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.rewriteStepCount :=
  AnalyticMotivesRoot.completedZetaResidueRectangle_homTargetRewriteStepCount
    R

/-- The scheduled-channel example morphism source endpoint carries the source rectangles. -/
theorem completedZetaExample_channelRectangleHom_sourceImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangles :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_homSourceImportedRectangles
    f
    F
    h
    u

/-- The scheduled-channel example morphism target endpoint carries the target rectangles. -/
theorem completedZetaExample_channelRectangleHom_targetImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangles :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_homTargetImportedRectangles
    f
    F
    h
    u

/-- The scheduled-channel example morphism source endpoint carries the source rectangle count. -/
theorem completedZetaExample_channelRectangleHom_sourceImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangleCount :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_homSourceImportedRectangleCount
    f
    F
    h
    u

/-- The scheduled-channel example morphism target endpoint carries the target rectangle count. -/
theorem completedZetaExample_channelRectangleHom_targetImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangleCount :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_homTargetImportedRectangleCount
    f
    F
    h
    u

/-- The scheduled-channel example morphism target imports exactly its listed rectangles. -/
theorem completedZetaExample_channelRectangleHom_targetImportedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles.length :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_homTargetRectangleCount_eq_length
    f
    F
    h
    u

/-- The scheduled-channel example morphism source endpoint carries trace bookkeeping. -/
theorem completedZetaExample_channelRectangleHom_sourceTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).traceBookkeepingCount :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_homSourceTraceBookkeepingCount
    f
    F
    h
    u

/-- The scheduled-channel example morphism target endpoint carries trace bookkeeping. -/
theorem completedZetaExample_channelRectangleHom_targetTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetTraceBookkeepingCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.traceBookkeepingCount :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_homTargetTraceBookkeepingCount
    f
    F
    h
    u

/-- The scheduled-channel example morphism source endpoint carries rewrite-step count. -/
theorem completedZetaExample_channelRectangleHom_sourceRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceRewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).rewriteStepCount :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_homSourceRewriteStepCount
    f
    F
    h
    u

/-- The scheduled-channel example morphism target endpoint carries rewrite-step count. -/
theorem completedZetaExample_channelRectangleHom_targetRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetRewriteStepCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.rewriteStepCount :=
  AnalyticMotivesRoot.completedZetaChannelRectangle_homTargetRewriteStepCount
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
