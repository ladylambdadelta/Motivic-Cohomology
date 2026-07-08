import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRectanglePipeline.Core.Owner

/-!
# Transport payload for the zero-pole rectangle pipeline

This file owns the rectangle, source, target, and transport-payload projection
facts for the rectangle-certified zero-pole residue pipeline.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The pipeline rectangle has center coordinate zero. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_rectangle_c
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_rectangle R).c =
      0 :=
  rfl

/-- The pipeline rectangle has height coordinate `R`. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_rectangle_T
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_rectangle R).T =
      R :=
  rfl

/-- The pipeline transport starts at the pipeline source. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_transport_source
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_transport R).source =
      completedZetaZeroPoleResidueRectanglePipeline_source R :=
  rfl

/-- The pipeline transport targets the pipeline target. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_transport_target
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_transport R).target =
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  rfl

/-- The pipeline transport carries the zero-pole residue path. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_transport_path
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_transport R).path =
      completedZetaZeroPoleResiduePath :=
  rfl

/-- The pipeline source presentation starts at the finite-square boundary expression. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_source_source
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_source R).source =
      completedZetaZeroPoleFiniteSquareBoundaryExpression :=
  completedZetaZeroPoleResiduePresentationWithRectangle_source R

/-- The pipeline target presentation starts at the finite-square residue expression. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_target_source :
    completedZetaZeroPoleResidueRectanglePipeline_target.source =
      completedZetaZeroPoleFiniteSquareResidueExpression :=
  completedZetaZeroPoleResidueOutput_source

/-- The pipeline transport path starts at the source presentation expression. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_transport_path_source
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_transport R).path.source =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).source :=
  (completedZetaZeroPoleResidueRectanglePipeline_transport R).path_source

/-- The pipeline transport path targets the target presentation expression. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_transport_path_target
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_transport R).path.target =
      completedZetaZeroPoleResidueRectanglePipeline_target.source :=
  (completedZetaZeroPoleResidueRectanglePipeline_transport R).path_target

/-- The pipeline source imports the original residue certificates plus the rectangle certificate. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_source_importedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount =
      completedZetaZeroPoleResiduePresentation.importedRectangleCount +
        (completedZetaZeroPoleFiniteSquareRectangleCertificateLedger R).importedRectangleCount :=
  completedZetaZeroPoleResiduePresentationWithRectangle_importedRectangleCount R

/-- The pipeline source keeps the original bookkeeping plus the rectangle ledger bookkeeping. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_source_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_source R).traceBookkeepingCount =
      completedZetaZeroPoleResiduePresentation.traceBookkeepingCount +
        (completedZetaZeroPoleFiniteSquareRectangleCertificateLedger R).traceBookkeepingCount :=
  completedZetaZeroPoleResiduePresentationWithRectangle_traceBookkeepingCount R

/-- The pipeline source contains the singleton imported finite-square rectangle certificate. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_source_rectangleCertificateCount
    (R : ℝ) :
    (completedZetaZeroPoleFiniteSquareRectangleCertificateLedger R).importedRectangleCount =
      1 + 0 :=
  completedZetaZeroPoleFiniteSquareRectangleCertificateLedger_importedRectangleCount R

/-- The pipeline transport payload splits into source, target, and rewrite-path certificates. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_transport_importedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_transport R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount +
        (completedZetaZeroPoleResidueRectanglePipeline_target.importedRectangleCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            completedZetaZeroPoleResiduePath).importedRectangleCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      (completedZetaZeroPoleResidueRectanglePipeline_source R).certificateLedger
      (ResidueChannelCertificateLedger.append
        completedZetaZeroPoleResidueRectanglePipeline_target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          completedZetaZeroPoleResiduePath)))
    (congrArg
      (fun count =>
        (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount +
          count)
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        completedZetaZeroPoleResidueRectanglePipeline_target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          completedZetaZeroPoleResiduePath)))

/-- The residue rewrite-path certificate carries no imported finite rectangle. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_rewritePath_importedRectangleCount :
    (ResidueChannelCertificateLedger.ofRewritePath
      completedZetaZeroPoleResiduePath).importedRectangleCount =
      0 + 0 :=
  rfl

/-- The residue rewrite-path certificate is one trace-bookkeeping atom. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_rewritePath_traceBookkeepingCount :
    (ResidueChannelCertificateLedger.ofRewritePath
      completedZetaZeroPoleResiduePath).traceBookkeepingCount =
      1 + 0 :=
  rfl

/-- The residue rewrite-path certificate records the residue path rewrite step. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_rewritePath_rewriteStepCount :
    (ResidueChannelCertificateLedger.ofRewritePath
      completedZetaZeroPoleResiduePath).rewriteStepCount =
      completedZetaZeroPoleResiduePath.stepCount + 0 :=
  rfl

/-- The pipeline transport bookkeeping splits into source, target, and rewrite-path certificates. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_transport_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_transport R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).traceBookkeepingCount +
        (completedZetaZeroPoleResidueRectanglePipeline_target.traceBookkeepingCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            completedZetaZeroPoleResiduePath).traceBookkeepingCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      (completedZetaZeroPoleResidueRectanglePipeline_source R).certificateLedger
      (ResidueChannelCertificateLedger.append
        completedZetaZeroPoleResidueRectanglePipeline_target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          completedZetaZeroPoleResiduePath)))
    (congrArg
      (fun count =>
        (completedZetaZeroPoleResidueRectanglePipeline_source R).traceBookkeepingCount +
          count)
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        completedZetaZeroPoleResidueRectanglePipeline_target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          completedZetaZeroPoleResiduePath)))

/-- The pipeline transport rewrite-step payload splits into source, target, and path certificates. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_transport_rewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_transport R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).rewriteStepCount +
        (completedZetaZeroPoleResidueRectanglePipeline_target.rewriteStepCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            completedZetaZeroPoleResiduePath).rewriteStepCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      (completedZetaZeroPoleResidueRectanglePipeline_source R).certificateLedger
      (ResidueChannelCertificateLedger.append
        completedZetaZeroPoleResidueRectanglePipeline_target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          completedZetaZeroPoleResiduePath)))
    (congrArg
      (fun count =>
        (completedZetaZeroPoleResidueRectanglePipeline_source R).rewriteStepCount +
          count)
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        completedZetaZeroPoleResidueRectanglePipeline_target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          completedZetaZeroPoleResiduePath)))

end AnalyticMotives
end LFunctions
end Boundary
