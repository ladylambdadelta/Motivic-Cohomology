import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.Payload.Owner

/-!
# Completed-zeta compact-geometric payload facade

This file gives completed-zeta adapter names to finite-rectangle endpoint
payload facts at the compact-geometric boundary.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The completed-zeta residue adapter source endpoint carries source rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homSourceImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homSourceImportedRectangles
    R

/-- The completed-zeta residue adapter target endpoint carries target rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homTargetImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homTargetImportedRectangles
    R

/-- The completed-zeta residue adapter source endpoint carries source rectangle count. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homSourceImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homSourceImportedRectangleCount
    R

/-- The completed-zeta residue adapter target endpoint carries target rectangle count. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homTargetImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homTargetImportedRectangleCount
    R

/-- The completed-zeta residue adapter target endpoint is counted by target rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homTargetRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles.length :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homTargetRectangleCount_eq_length
    R

/-- The completed-zeta residue adapter source endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homSourceTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homSourceTraceBookkeepingCount
    R

/-- The completed-zeta residue adapter target endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homTargetTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetTraceBookkeepingCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homTargetTraceBookkeepingCount
    R

/-- The completed-zeta residue adapter source endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homSourceRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceRewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homSourceRewriteStepCount
    R

/-- The completed-zeta residue adapter target endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homTargetRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetRewriteStepCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homTargetRewriteStepCount
    R

/-- The completed-zeta channel adapter source endpoint carries source rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homSourceImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homSourceImportedRectangles
    f
    F
    h
    u

/-- The completed-zeta channel adapter target endpoint carries target rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homTargetImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homTargetImportedRectangles
    f
    F
    h
    u

/-- The completed-zeta channel adapter source endpoint carries source rectangle count. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homSourceImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homSourceImportedRectangleCount
    f
    F
    h
    u

/-- The completed-zeta channel adapter target endpoint carries target rectangle count. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homTargetImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homTargetImportedRectangleCount
    f
    F
    h
    u

/-- The completed-zeta channel adapter target endpoint is counted by target rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homTargetRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles.length :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homTargetRectangleCount_eq_length
    f
    F
    h
    u

/-- The completed-zeta channel adapter source endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homSourceTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homSourceTraceBookkeepingCount
    f
    F
    h
    u

/-- The completed-zeta channel adapter target endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homTargetTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetTraceBookkeepingCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homTargetTraceBookkeepingCount
    f
    F
    h
    u

/-- The completed-zeta channel adapter source endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homSourceRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceRewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homSourceRewriteStepCount
    f
    F
    h
    u

/-- The completed-zeta channel adapter target endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homTargetRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetRewriteStepCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homTargetRewriteStepCount
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
