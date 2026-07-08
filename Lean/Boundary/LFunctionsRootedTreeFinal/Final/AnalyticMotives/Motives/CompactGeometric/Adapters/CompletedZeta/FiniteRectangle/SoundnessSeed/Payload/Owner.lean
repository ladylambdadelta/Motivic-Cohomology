import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ResidueRectangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ChannelRectangle.Owner

/-!
# Compact-geometric completed-zeta adapter payload

This file exposes endpoint imported-rectangle and trace-calculus payload facts
at the compact-geometric adapter boundary.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The compact-geometric residue morphism source endpoint carries the source rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangles :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_sourceImportedRectangles
    R

/-- The compact-geometric residue morphism target endpoint carries the target rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangles :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_targetImportedRectangles
    R

/-- The compact-geometric residue morphism source endpoint carries the source rectangle count. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_sourceImportedRectangleCount
    R

/-- The compact-geometric residue morphism target endpoint carries the target rectangle count. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangleCount :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_targetImportedRectangleCount
    R

/-- The compact-geometric residue morphism target endpoint is counted by its rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles.length :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_targetImportedRectangleCount_eq_length
    R

/-- The compact-geometric residue morphism source endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).traceBookkeepingCount :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_sourceTraceBookkeepingCount
    R

/-- The compact-geometric residue morphism target endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetTraceBookkeepingCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.traceBookkeepingCount :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_targetTraceBookkeepingCount
    R

/-- The compact-geometric residue morphism source endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceRewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).rewriteStepCount :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_sourceRewriteStepCount
    R

/-- The compact-geometric residue morphism target endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetRewriteStepCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.rewriteStepCount :=
  completedZetaZeroPoleResidueRectangleGeneratorHom_targetRewriteStepCount
    R

/-- The compact-geometric scheduled-channel morphism source endpoint carries the source rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangles :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_sourceImportedRectangles
    f
    F
    h
    u

/-- The compact-geometric scheduled-channel morphism target endpoint carries the target rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangles :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_targetImportedRectangles
    f
    F
    h
    u

/-- The compact-geometric scheduled-channel morphism source endpoint carries the source rectangle count. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangleCount :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_sourceImportedRectangleCount
    f
    F
    h
    u

/-- The compact-geometric scheduled-channel morphism target endpoint carries the target rectangle count. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangleCount :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_targetImportedRectangleCount
    f
    F
    h
    u

/-- The compact-geometric scheduled-channel morphism target endpoint is counted by its rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles.length :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_targetImportedRectangleCount_eq_length
    f
    F
    h
    u

/-- The compact-geometric scheduled-channel morphism source endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).traceBookkeepingCount :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_sourceTraceBookkeepingCount
    f
    F
    h
    u

/-- The compact-geometric scheduled-channel morphism target endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetTraceBookkeepingCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.traceBookkeepingCount :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_targetTraceBookkeepingCount
    f
    F
    h
    u

/-- The compact-geometric scheduled-channel morphism source endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceRewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).rewriteStepCount :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_sourceRewriteStepCount
    f
    F
    h
    u

/-- The compact-geometric scheduled-channel morphism target endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetRewriteStepCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.rewriteStepCount :=
  completedZetaZeroPoleChannelRectangleGeneratorHom_targetRewriteStepCount
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
