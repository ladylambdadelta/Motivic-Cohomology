import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Payload.Owner

/-!
# Motive-root completed-zeta compact adapter payload

This file exposes endpoint imported-rectangle and trace-calculus payload facts
for the completed-zeta finite-rectangle compact morphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The residue rectangle compact morphism source endpoint carries the source rectangles. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_homSourceImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceImportedRectangles
    R

/-- The residue rectangle compact morphism target endpoint carries the target rectangles. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_homTargetImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetImportedRectangles
    R

/-- The residue rectangle compact morphism source endpoint carries the source rectangle count. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_homSourceImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceImportedRectangleCount
    R

/-- The residue rectangle compact morphism target endpoint carries the target rectangle count. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_homTargetImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetImportedRectangleCount
    R

/-- The residue rectangle compact morphism target endpoint is counted by its rectangles. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_homTargetRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles.length :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetRectangleCount_eq_length
    R

/-- The residue rectangle compact morphism source endpoint carries trace bookkeeping. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_homSourceTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceTraceBookkeepingCount
    R

/-- The residue rectangle compact morphism target endpoint carries trace bookkeeping. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_homTargetTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetTraceBookkeepingCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetTraceBookkeepingCount
    R

/-- The residue rectangle compact morphism source endpoint carries rewrite-step count. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_homSourceRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceRewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceRewriteStepCount
    R

/-- The residue rectangle compact morphism target endpoint carries rewrite-step count. -/
theorem TraceAnalyticMotive.completedZetaResidueRectangle_homTargetRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetRewriteStepCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetRewriteStepCount
    R

/-- The scheduled-channel compact morphism source endpoint carries the source rectangles. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_homSourceImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceImportedRectangles
    f
    F
    h
    u

/-- The scheduled-channel compact morphism target endpoint carries the target rectangles. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_homTargetImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetImportedRectangles
    f
    F
    h
    u

/-- The scheduled-channel compact morphism source endpoint carries the source rectangle count. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_homSourceImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceImportedRectangleCount
    f
    F
    h
    u

/-- The scheduled-channel compact morphism target endpoint carries the target rectangle count. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_homTargetImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetImportedRectangleCount
    f
    F
    h
    u

/-- The scheduled-channel compact morphism target endpoint is counted by its rectangles. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_homTargetRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles.length :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetRectangleCount_eq_length
    f
    F
    h
    u

/-- The scheduled-channel compact morphism source endpoint carries trace bookkeeping. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_homSourceTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceTraceBookkeepingCount
    f
    F
    h
    u

/-- The scheduled-channel compact morphism target endpoint carries trace bookkeeping. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_homTargetTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetTraceBookkeepingCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetTraceBookkeepingCount
    f
    F
    h
    u

/-- The scheduled-channel compact morphism source endpoint carries rewrite-step count. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_homSourceRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceRewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceRewriteStepCount
    f
    F
    h
    u

/-- The scheduled-channel compact morphism target endpoint carries rewrite-step count. -/
theorem TraceAnalyticMotive.completedZetaChannelRectangle_homTargetRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetRewriteStepCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetRewriteStepCount
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
