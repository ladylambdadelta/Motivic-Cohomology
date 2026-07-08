import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectanglePipeline.Core.Owner

/-!
# Transport payload for the zero-pole scheduled-channel rectangle pipeline

This file owns the rectangle, source, rewrite-path, and transport-payload
projection facts for the scheduled-channel rectangle pipeline.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The pipeline rectangle has center coordinate zero. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangle_c
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangle
      f F h u).c =
      0 :=
  rfl

/-- The pipeline rectangle has the scheduled height. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangle_T
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangle
      f F h u).T =
      h.height_schedule.height u :=
  rfl

/-- The pipeline rectangle ledger records one imported finite rectangle. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangleLedger_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangleLedger
      f F h u).importedRectangleCount =
      1 + 0 :=
  completedZetaZeroPoleScheduledChannelRectangleCertificateLedger_importedRectangleCount
    f F h u

/-- The pipeline rectangle ledger has no internal trace-bookkeeping atom. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangleLedger_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangleLedger
      f F h u).traceBookkeepingCount =
      0 + 0 :=
  completedZetaZeroPoleScheduledChannelRectangleCertificateLedger_traceBookkeepingCount
    f F h u

/-- The pipeline source imports the original channel certificates plus the scheduled rectangle. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_source_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
      f F h u).importedRectangleCount =
      completedZetaZeroPoleChannelPresentation.importedRectangleCount +
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangleLedger
          f F h u).importedRectangleCount :=
  completedZetaZeroPoleChannelPresentationWithScheduledRectangle_importedRectangleCount
    f F h u

/-- The pipeline source bookkeeping is the original bookkeeping plus scheduled-rectangle bookkeeping. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_source_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
      f F h u).traceBookkeepingCount =
      completedZetaZeroPoleChannelPresentation.traceBookkeepingCount +
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangleLedger
          f F h u).traceBookkeepingCount :=
  completedZetaZeroPoleChannelPresentationWithScheduledRectangle_traceBookkeepingCount
    f F h u

/-- The channel rewrite-path certificate carries no imported finite rectangle. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_rewritePath_importedRectangleCount :
    (ResidueChannelCertificateLedger.ofRewritePath
      completedZetaZeroPoleChannelPath).importedRectangleCount =
      0 + 0 :=
  rfl

/-- The channel rewrite-path certificate is one trace-bookkeeping atom. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_rewritePath_traceBookkeepingCount :
    (ResidueChannelCertificateLedger.ofRewritePath
      completedZetaZeroPoleChannelPath).traceBookkeepingCount =
      1 + 0 :=
  rfl

/-- The channel rewrite-path certificate records the channel path rewrite step. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_rewritePath_rewriteStepCount :
    (ResidueChannelCertificateLedger.ofRewritePath
      completedZetaZeroPoleChannelPath).rewriteStepCount =
      completedZetaZeroPoleChannelPath.stepCount + 0 :=
  rfl

/-- The pipeline transport payload splits into source, target, and rewrite-path certificates. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_transport_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).importedRectangleCount +
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_target.importedRectangleCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            completedZetaZeroPoleChannelPath).importedRectangleCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).certificateLedger
      (ResidueChannelCertificateLedger.append
        completedZetaZeroPoleChannelScheduledRectanglePipeline_target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          completedZetaZeroPoleChannelPath)))
    (congrArg
      (fun count =>
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
          f F h u).importedRectangleCount +
          count)
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        completedZetaZeroPoleChannelScheduledRectanglePipeline_target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          completedZetaZeroPoleChannelPath)))

/-- The pipeline transport bookkeeping splits into source, target, and rewrite-path certificates. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_transport_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).traceBookkeepingCount +
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_target.traceBookkeepingCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            completedZetaZeroPoleChannelPath).traceBookkeepingCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).certificateLedger
      (ResidueChannelCertificateLedger.append
        completedZetaZeroPoleChannelScheduledRectanglePipeline_target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          completedZetaZeroPoleChannelPath)))
    (congrArg
      (fun count =>
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
          f F h u).traceBookkeepingCount +
          count)
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        completedZetaZeroPoleChannelScheduledRectanglePipeline_target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          completedZetaZeroPoleChannelPath)))

/-- The pipeline transport rewrite-step payload splits into source, target, and path certificates. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_transport_rewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).rewriteStepCount +
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_target.rewriteStepCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            completedZetaZeroPoleChannelPath).rewriteStepCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).certificateLedger
      (ResidueChannelCertificateLedger.append
        completedZetaZeroPoleChannelScheduledRectanglePipeline_target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          completedZetaZeroPoleChannelPath)))
    (congrArg
      (fun count =>
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
          f F h u).rewriteStepCount +
          count)
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        completedZetaZeroPoleChannelScheduledRectanglePipeline_target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          completedZetaZeroPoleChannelPath)))

/-- The pipeline transport starts at the pipeline source. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_transport_source
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
      f F h u).source =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u :=
  rfl

/-- The pipeline transport targets the pipeline target. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_transport_target
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
      f F h u).target =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  rfl

/-- The pipeline transport carries the channel path. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_transport_path
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
      f F h u).path =
      completedZetaZeroPoleChannelPath :=
  rfl

/-- The pipeline transport path starts at the source presentation expression. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_transport_path_source
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
      f F h u).path.source =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).source :=
  (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
    f F h u).path_source

/-- The pipeline transport path targets the target presentation expression. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_transport_path_target
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
      f F h u).path.target =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.source :=
  (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
    f F h u).path_target

end AnalyticMotives
end LFunctions
end Boundary
