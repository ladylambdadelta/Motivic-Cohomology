import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.Payload.Owner

/-!
# Completed-zeta finite-rectangle compact-geometric payload facade

This file gives finite-rectangle names to the completed-zeta compact-geometric
endpoint payload facts.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The finite-rectangle residue compact morphism source endpoint carries source rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homSourceImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceImportedRectangles
    R

/-- The finite-rectangle residue compact morphism target endpoint carries target rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homTargetImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetImportedRectangles
    R

/-- The finite-rectangle residue compact morphism source endpoint carries source rectangle count. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homSourceImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceImportedRectangleCount
    R

/-- The finite-rectangle residue compact morphism target endpoint carries target rectangle count. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homTargetImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetImportedRectangleCount
    R

/-- The finite-rectangle residue compact morphism target endpoint is counted by target rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homTargetRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles.length :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetRectangleCount_eq_length
    R

/-- The finite-rectangle residue compact morphism source endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homSourceTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceTraceBookkeepingCount
    R

/-- The finite-rectangle residue compact morphism target endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homTargetTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetTraceBookkeepingCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetTraceBookkeepingCount
    R

/-- The finite-rectangle residue compact morphism source endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homSourceRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceRewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homSourceRewriteStepCount
    R

/-- The finite-rectangle residue compact morphism target endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleResidue_homTargetRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetRewriteStepCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaResidueRectangle_homTargetRewriteStepCount
    R

/-- The finite-rectangle scheduled-channel compact morphism source endpoint carries source rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homSourceImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceImportedRectangles
    f
    F
    h
    u

/-- The finite-rectangle scheduled-channel compact morphism target endpoint carries target rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homTargetImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangles :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetImportedRectangles
    f
    F
    h
    u

/-- The finite-rectangle scheduled-channel compact morphism source endpoint carries source rectangle count. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homSourceImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceImportedRectangleCount
    f
    F
    h
    u

/-- The finite-rectangle scheduled-channel compact morphism target endpoint carries target rectangle count. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homTargetImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangleCount :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetImportedRectangleCount
    f
    F
    h
    u

/-- The finite-rectangle scheduled-channel compact morphism target endpoint is counted by target rectangles. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homTargetRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles.length :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetRectangleCount_eq_length
    f
    F
    h
    u

/-- The finite-rectangle scheduled-channel compact morphism source endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homSourceTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceTraceBookkeepingCount
    f
    F
    h
    u

/-- The finite-rectangle scheduled-channel compact morphism target endpoint carries trace bookkeeping. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homTargetTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetTraceBookkeepingCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.traceBookkeepingCount :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homTargetTraceBookkeepingCount
    f
    F
    h
    u

/-- The finite-rectangle scheduled-channel compact morphism source endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homSourceRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceRewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).rewriteStepCount :=
  TraceAnalyticCompactGeometric.completedZetaChannelRectangle_homSourceRewriteStepCount
    f
    F
    h
    u

/-- The finite-rectangle scheduled-channel compact morphism target endpoint carries rewrite-step count. -/
theorem TraceAnalyticCompactGeometric.completedZetaFiniteRectangleChannel_homTargetRewriteStepCount
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
