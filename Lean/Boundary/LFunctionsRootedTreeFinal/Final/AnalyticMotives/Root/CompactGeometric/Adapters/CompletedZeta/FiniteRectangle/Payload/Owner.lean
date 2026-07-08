import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Adapters.CompletedZeta.FiniteRectangle.Payload.Owner

/-!
# Top-root completed-zeta finite-rectangle payload facade

This file mirrors finite-rectangle endpoint payload facts under the
`AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes finite-rectangle residue source imported rectangles. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_homSourceImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangles :=
  TraceAnalyticMotive.completedZetaFiniteRectangleResidue_homSourceImportedRectangles
    R

/-- The analytic-motives root exposes finite-rectangle residue target imported rectangles. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_homTargetImportedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangles :=
  TraceAnalyticMotive.completedZetaFiniteRectangleResidue_homTargetImportedRectangles
    R

/-- The analytic-motives root exposes finite-rectangle residue source imported-rectangle count. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_homSourceImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceImportedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount :=
  TraceAnalyticMotive.completedZetaFiniteRectangleResidue_homSourceImportedRectangleCount
    R

/-- The analytic-motives root exposes finite-rectangle residue target imported-rectangle count. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_homTargetImportedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangleCount :=
  TraceAnalyticMotive.completedZetaFiniteRectangleResidue_homTargetImportedRectangleCount
    R

/-- The analytic-motives root exposes finite-rectangle residue target count-as-length. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_homTargetRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangleCount =
      (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetImportedRectangles.length :=
  TraceAnalyticMotive.completedZetaFiniteRectangleResidue_homTargetRectangleCount_eq_length
    R

/-- The analytic-motives root exposes finite-rectangle residue source trace bookkeeping. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_homSourceTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).traceBookkeepingCount :=
  TraceAnalyticMotive.completedZetaFiniteRectangleResidue_homSourceTraceBookkeepingCount
    R

/-- The analytic-motives root exposes finite-rectangle residue target trace bookkeeping. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_homTargetTraceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetTraceBookkeepingCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.traceBookkeepingCount :=
  TraceAnalyticMotive.completedZetaFiniteRectangleResidue_homTargetTraceBookkeepingCount
    R

/-- The analytic-motives root exposes finite-rectangle residue source rewrite-step count. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_homSourceRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).sourceRewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).rewriteStepCount :=
  TraceAnalyticMotive.completedZetaFiniteRectangleResidue_homSourceRewriteStepCount
    R

/-- The analytic-motives root exposes finite-rectangle residue target rewrite-step count. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleResidue_homTargetRewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectangleGeneratorHom R).targetRewriteStepCount =
      completedZetaZeroPoleResidueRectanglePipeline_target.rewriteStepCount :=
  TraceAnalyticMotive.completedZetaFiniteRectangleResidue_homTargetRewriteStepCount
    R

/-- The analytic-motives root exposes finite-rectangle channel source imported rectangles. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_homSourceImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangles :=
  TraceAnalyticMotive.completedZetaFiniteRectangleChannel_homSourceImportedRectangles
    f
    F
    h
    u

/-- The analytic-motives root exposes finite-rectangle channel target imported rectangles. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_homTargetImportedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangles :=
  TraceAnalyticMotive.completedZetaFiniteRectangleChannel_homTargetImportedRectangles
    f
    F
    h
    u

/-- The analytic-motives root exposes finite-rectangle channel source imported-rectangle count. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_homSourceImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceImportedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).importedRectangleCount :=
  TraceAnalyticMotive.completedZetaFiniteRectangleChannel_homSourceImportedRectangleCount
    f
    F
    h
    u

/-- The analytic-motives root exposes finite-rectangle channel target imported-rectangle count. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_homTargetImportedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangleCount :=
  TraceAnalyticMotive.completedZetaFiniteRectangleChannel_homTargetImportedRectangleCount
    f
    F
    h
    u

/-- The analytic-motives root exposes finite-rectangle channel target count-as-length. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_homTargetRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangleCount =
      (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetImportedRectangles.length :=
  TraceAnalyticMotive.completedZetaFiniteRectangleChannel_homTargetRectangleCount_eq_length
    f
    F
    h
    u

/-- The analytic-motives root exposes finite-rectangle channel source trace bookkeeping. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_homSourceTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceTraceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).traceBookkeepingCount :=
  TraceAnalyticMotive.completedZetaFiniteRectangleChannel_homSourceTraceBookkeepingCount
    f
    F
    h
    u

/-- The analytic-motives root exposes finite-rectangle channel target trace bookkeeping. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_homTargetTraceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetTraceBookkeepingCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.traceBookkeepingCount :=
  TraceAnalyticMotive.completedZetaFiniteRectangleChannel_homTargetTraceBookkeepingCount
    f
    F
    h
    u

/-- The analytic-motives root exposes finite-rectangle channel source rewrite-step count. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_homSourceRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).sourceRewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u).rewriteStepCount :=
  TraceAnalyticMotive.completedZetaFiniteRectangleChannel_homSourceRewriteStepCount
    f
    F
    h
    u

/-- The analytic-motives root exposes finite-rectangle channel target rewrite-step count. -/
theorem AnalyticMotivesRoot.completedZetaFiniteRectangleChannel_homTargetRewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelRectangleGeneratorHom f F h u).targetRewriteStepCount =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.rewriteStepCount :=
  TraceAnalyticMotive.completedZetaFiniteRectangleChannel_homTargetRewriteStepCount
    f
    F
    h
    u

end AnalyticMotives
end LFunctions
end Boundary
