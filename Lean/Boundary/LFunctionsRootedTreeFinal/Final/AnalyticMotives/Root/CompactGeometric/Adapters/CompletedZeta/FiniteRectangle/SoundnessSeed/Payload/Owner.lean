import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Payload.Owner

/-!
# Top-root completed-zeta compact adapter payload

This file exposes endpoint imported-rectangle and trace-calculus payload facts
for the completed-zeta finite-rectangle compact morphisms under the top-level
`AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The residue rectangle compact morphism source endpoint carries the source rectangles. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_homSourceImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangles :=
  TraceAnalyticMotive.completedZetaResidueRectangle_homSourceImportedRectangles
    R

/-- The residue rectangle compact morphism target endpoint carries the target rectangles. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_homTargetImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangles :=
  TraceAnalyticMotive.completedZetaResidueRectangle_homTargetImportedRectangles
    R

/-- The residue rectangle compact morphism source endpoint carries the source rectangle count. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_homSourceImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount :=
  TraceAnalyticMotive.completedZetaResidueRectangle_homSourceImportedRectangleCount
    R

/-- The residue rectangle compact morphism target endpoint carries the target rectangle count. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_homTargetImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangleCount :=
  TraceAnalyticMotive.completedZetaResidueRectangle_homTargetImportedRectangleCount
    R

/-- The residue rectangle compact morphism target endpoint is counted by its rectangles. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_homTargetRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles.length :=
  TraceAnalyticMotive.completedZetaResidueRectangle_homTargetRectangleCount_eq_length
    R

/-- The residue rectangle compact morphism source endpoint carries trace bookkeeping. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_homSourceTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).traceBookkeepingCount :=
  TraceAnalyticMotive.completedZetaResidueRectangle_homSourceTraceBookkeepingCount
    R

/-- The residue rectangle compact morphism target endpoint carries trace bookkeeping. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_homTargetTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetTraceBookkeepingCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.traceBookkeepingCount :=
  TraceAnalyticMotive.completedZetaResidueRectangle_homTargetTraceBookkeepingCount
    R

/-- The residue rectangle compact morphism source endpoint carries rewrite-step count. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_homSourceRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceRewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).rewriteStepCount :=
  TraceAnalyticMotive.completedZetaResidueRectangle_homSourceRewriteStepCount
    R

/-- The residue rectangle compact morphism target endpoint carries rewrite-step count. -/
theorem AnalyticMotivesRoot.completedZetaResidueRectangle_homTargetRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetRewriteStepCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.rewriteStepCount :=
  TraceAnalyticMotive.completedZetaResidueRectangle_homTargetRewriteStepCount
    R

/-- The scheduled-channel compact morphism source endpoint carries the source rectangles. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_homSourceImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangles :=
  TraceAnalyticMotive.completedZetaChannelRectangle_homSourceImportedRectangles
    f
    F
    h
    u

/-- The scheduled-channel compact morphism target endpoint carries the target rectangles. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_homTargetImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangles :=
  TraceAnalyticMotive.completedZetaChannelRectangle_homTargetImportedRectangles
    f
    F
    h
    u

/-- The scheduled-channel compact morphism source endpoint carries the source rectangle count. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_homSourceImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangleCount :=
  TraceAnalyticMotive.completedZetaChannelRectangle_homSourceImportedRectangleCount
    f
    F
    h
    u

/-- The scheduled-channel compact morphism target endpoint carries the target rectangle count. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_homTargetImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangleCount :=
  TraceAnalyticMotive.completedZetaChannelRectangle_homTargetImportedRectangleCount
    f
    F
    h
    u

/-- The scheduled-channel compact morphism target endpoint is counted by its rectangles. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_homTargetRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles.length :=
  TraceAnalyticMotive.completedZetaChannelRectangle_homTargetRectangleCount_eq_length
    f
    F
    h
    u

/-- The scheduled-channel compact morphism source endpoint carries trace bookkeeping. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_homSourceTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).traceBookkeepingCount :=
  TraceAnalyticMotive.completedZetaChannelRectangle_homSourceTraceBookkeepingCount
    f
    F
    h
    u

/-- The scheduled-channel compact morphism target endpoint carries trace bookkeeping. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_homTargetTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetTraceBookkeepingCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.traceBookkeepingCount :=
  TraceAnalyticMotive.completedZetaChannelRectangle_homTargetTraceBookkeepingCount
    f
    F
    h
    u

/-- The scheduled-channel compact morphism source endpoint carries rewrite-step count. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_homSourceRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceRewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).rewriteStepCount :=
  TraceAnalyticMotive.completedZetaChannelRectangle_homSourceRewriteStepCount
    f
    F
    h
    u

/-- The scheduled-channel compact morphism target endpoint carries rewrite-step count. -/
theorem AnalyticMotivesRoot.completedZetaChannelRectangle_homTargetRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetRewriteStepCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.rewriteStepCount :=
  TraceAnalyticMotive.completedZetaChannelRectangle_homTargetRewriteStepCount
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
