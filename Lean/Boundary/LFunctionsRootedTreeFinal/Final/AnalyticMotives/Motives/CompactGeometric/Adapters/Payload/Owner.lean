import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.CompletedZeta.Payload.Owner

/-!
# Compact-geometric adapter payload facade

This file exposes endpoint payload facts at the generic compact-geometric
adapter boundary.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The compact-geometric residue adapter source endpoint carries source rectangles. -/
theorem TraceAnalyticCompactGeometric.adapterResidue_homSourceImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homSourceImportedRectangles
    R

/-- The compact-geometric residue adapter target endpoint carries target rectangles. -/
theorem TraceAnalyticCompactGeometric.adapterResidue_homTargetImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homTargetImportedRectangles
    R

/-- The compact-geometric residue adapter source endpoint carries source rectangle count. -/
theorem TraceAnalyticCompactGeometric.adapterResidue_homSourceImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homSourceImportedRectangleCount
    R

/-- The compact-geometric residue adapter target endpoint carries target rectangle count. -/
theorem TraceAnalyticCompactGeometric.adapterResidue_homTargetImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homTargetImportedRectangleCount
    R

/-- The compact-geometric residue adapter target endpoint is counted by target rectangles. -/
theorem TraceAnalyticCompactGeometric.adapterResidue_homTargetRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles.length :=
  TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homTargetRectangleCount_eq_length
    R

/-- The compact-geometric residue adapter source endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.adapterResidue_homSourceTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homSourceTraceBookkeepingCount
    R

/-- The compact-geometric residue adapter target endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.adapterResidue_homTargetTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetTraceBookkeepingCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homTargetTraceBookkeepingCount
    R

/-- The compact-geometric residue adapter source endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.adapterResidue_homSourceRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceRewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homSourceRewriteStepCount
    R

/-- The compact-geometric residue adapter target endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.adapterResidue_homTargetRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetRewriteStepCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaAdapterResidue_homTargetRewriteStepCount
    R

/-- The compact-geometric channel adapter source endpoint carries source rectangles. -/
theorem TraceAnalyticCompactGeometric.adapterChannel_homSourceImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homSourceImportedRectangles
    f
    F
    h
    u

/-- The compact-geometric channel adapter target endpoint carries target rectangles. -/
theorem TraceAnalyticCompactGeometric.adapterChannel_homTargetImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homTargetImportedRectangles
    f
    F
    h
    u

/-- The compact-geometric channel adapter source endpoint carries source rectangle count. -/
theorem TraceAnalyticCompactGeometric.adapterChannel_homSourceImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homSourceImportedRectangleCount
    f
    F
    h
    u

/-- The compact-geometric channel adapter target endpoint carries target rectangle count. -/
theorem TraceAnalyticCompactGeometric.adapterChannel_homTargetImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homTargetImportedRectangleCount
    f
    F
    h
    u

/-- The compact-geometric channel adapter target endpoint is counted by target rectangles. -/
theorem TraceAnalyticCompactGeometric.adapterChannel_homTargetRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles.length :=
  TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homTargetRectangleCount_eq_length
    f
    F
    h
    u

/-- The compact-geometric channel adapter source endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.adapterChannel_homSourceTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homSourceTraceBookkeepingCount
    f
    F
    h
    u

/-- The compact-geometric channel adapter target endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.adapterChannel_homTargetTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetTraceBookkeepingCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homTargetTraceBookkeepingCount
    f
    F
    h
    u

/-- The compact-geometric channel adapter source endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.adapterChannel_homSourceRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceRewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homSourceRewriteStepCount
    f
    F
    h
    u

/-- The compact-geometric channel adapter target endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.adapterChannel_homTargetRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetRewriteStepCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaAdapterChannel_homTargetRewriteStepCount
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
