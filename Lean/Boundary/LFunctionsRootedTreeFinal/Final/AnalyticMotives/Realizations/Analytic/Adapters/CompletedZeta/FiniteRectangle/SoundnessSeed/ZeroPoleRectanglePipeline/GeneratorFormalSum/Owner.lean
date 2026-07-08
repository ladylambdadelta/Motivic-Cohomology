import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRectanglePipeline.TransportPayload.Owner

/-!
# Generator and formal-sum projections for the zero-pole rectangle pipeline

This file records the generator, typed-term, and typed-formal-sum projection
facts for the rectangle-certified completed-zeta zero-pole residue pipeline.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The pipeline generator starts at the pipeline source. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_generator_source
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_generator R).source =
      completedZetaZeroPoleResidueRectanglePipeline_source R :=
  rfl

/-- The pipeline generator targets the pipeline target. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_generator_target
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_generator R).target =
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  rfl

/-- The pipeline generator carries the zero-pole residue path. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_generator_path
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_generator R).path =
      completedZetaZeroPoleResiduePath :=
  rfl

/-- The pipeline generator path starts at the source presentation expression. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_generator_path_source
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_generator R).path.source =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).source :=
  (completedZetaZeroPoleResidueRectanglePipeline_generator R).path_source

/-- The pipeline generator path targets the target presentation expression. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_generator_path_target
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_generator R).path.target =
      completedZetaZeroPoleResidueRectanglePipeline_target.source :=
  (completedZetaZeroPoleResidueRectanglePipeline_generator R).path_target

/-- The pipeline typed term has coefficient one. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_term_coefficient
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_term R).coefficient =
      1 :=
  rfl

/-- The pipeline typed term has the pipeline generator. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_term_generator
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_term R).generator =
      completedZetaZeroPoleResidueRectanglePipeline_generator R :=
  rfl

/-- Forgetting endpoints from the pipeline typed formal sum gives the raw singleton. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_raw
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).raw =
      completedZetaZeroPoleResidueRectangleTraceCorQFormalSum R :=
  rfl

/-- The pipeline typed formal sum has the upstream typed formal-sum certificate ledger. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_certificateLedger
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).certificateLedger =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).certificateLedger :=
  rfl

/-- The pipeline generator carries the rectangle-certified generator ledger. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_generator_certificateLedger
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_generator R).certificateLedger =
      (completedZetaZeroPoleResidueRectangleTraceCorQGenerator R).certificateLedger :=
  rfl

/-- The pipeline generator imported payload is the rectangle-certified generator payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_generator_importedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_generator R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQGenerator R).importedRectangleCount :=
  rfl

/-- The pipeline generator rectangle list is the rectangle-certified generator rectangle list. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_generator_importedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_generator R).importedRectangles =
      (completedZetaZeroPoleResidueRectangleTraceCorQGenerator R).importedRectangles :=
  rfl

/-- The pipeline generator bookkeeping payload is the rectangle-certified generator payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_generator_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_generator R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQGenerator R).traceBookkeepingCount :=
  rfl

/-- The pipeline generator rewrite-step payload is the rectangle-certified generator payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_generator_rewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_generator R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQGenerator R).rewriteStepCount :=
  rfl

/-- The pipeline typed term carries the pipeline generator ledger. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_term_certificateLedger
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_term R).certificateLedger =
      (completedZetaZeroPoleResidueRectanglePipeline_generator R).certificateLedger :=
  rfl

/-- The pipeline typed term imported payload is the pipeline generator payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_term_importedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_term R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_generator R).importedRectangleCount :=
  rfl

/-- The pipeline typed term rectangle list is the pipeline generator rectangle list. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_term_importedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_term R).importedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_generator R).importedRectangles :=
  rfl

/-- The pipeline typed term bookkeeping payload is the pipeline generator payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_term_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_term R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_generator R).traceBookkeepingCount :=
  rfl

/-- The pipeline typed term rewrite-step payload is the pipeline generator payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_term_rewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_term R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_generator R).rewriteStepCount :=
  rfl

/-- The pipeline formal sum imported payload is the upstream typed formal-sum payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_importedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).importedRectangleCount :=
  rfl

/-- The pipeline formal sum rectangle list is the upstream typed formal-sum rectangle list. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_importedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangles =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).importedRectangles :=
  rfl

/-- The pipeline formal sum bookkeeping payload is the upstream typed formal-sum payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).traceBookkeepingCount :=
  rfl

/-- The pipeline formal sum rewrite-step payload is the upstream typed formal-sum payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_rewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).rewriteStepCount :=
  rfl

/-- The pipeline typed singleton imports the payload carried by its generator. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_importedRectangleCount_eq_generator
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_generator R).importedRectangleCount +
        0 :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangleCount
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum_certificateLedger R))
    (completedZetaZeroPoleResidueRectangleTraceCorQFormalSum_importedRectangleCount R)

/-- The pipeline typed singleton exposes the rectangle list carried by its generator. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_importedRectangles_eq_generator
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_generator R).importedRectangles ++
        ResidueChannelCertificateLedger.empty.importedRectangles :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangles
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum_certificateLedger R))
    (completedZetaZeroPoleResidueRectangleTraceCorQFormalSum_importedRectangles R)

/-- The pipeline typed singleton keeps the bookkeeping carried by its generator. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_traceBookkeepingCount_eq_generator
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_generator R).traceBookkeepingCount +
        0 :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.traceBookkeepingCount
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum_certificateLedger R))
    (completedZetaZeroPoleResidueRectangleTraceCorQFormalSum_traceBookkeepingCount R)

/-- The pipeline typed singleton keeps the rewrite steps carried by its generator. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_rewriteStepCount_eq_generator
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_generator R).rewriteStepCount +
        0 :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.rewriteStepCount
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum_certificateLedger R))
    (completedZetaZeroPoleResidueRectangleTraceCorQFormalSum_rewriteStepCount R)

end AnalyticMotives
end LFunctions
end Boundary
