import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRectangleTypedClass.Owner

/-!
# Zero-pole rectangle-certified pipeline

This file collects the end-to-end data for the first rectangle-certified
completed-zeta residue trace correspondence.

It does not introduce new structure.  Each declaration is a named projection
of the concrete rectangle-certified presentation, transport, generator, typed
hom, representative, candidate, and quotient already constructed upstream.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The rectangle certificate used by the completed-zeta zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_rectangle
    (R : ℝ) :
    ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  completedZetaZeroPoleFiniteSquareRectangle R

/-- The source presentation of the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_source
    (R : ℝ) :
    TraceCorQObject :=
  completedZetaZeroPoleResidueRectangleHomSource R

/-- The target presentation of the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_target :
    TraceCorQObject :=
  completedZetaZeroPoleResidueRectangleHomTarget

/-- The transport used by the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_transport
    (R : ℝ) :
    TraceTransport :=
  completedZetaZeroPoleResidueTransportWithRectangle R

/-- The generator used by the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_generator
    (R : ℝ) :
    TraceCorQGenerator :=
  completedZetaZeroPoleResidueRectangleTraceCorQGenerator R

/-- The typed term used by the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_term
    (R : ℝ) :
    TraceCorQHomTerm
      (completedZetaZeroPoleResidueRectanglePipeline_source R)
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  completedZetaZeroPoleResidueRectangleTraceCorQHomTerm R

/-- The typed formal sum used by the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_formalSum
    (R : ℝ) :
    TraceCorQHomFormalSum
      (completedZetaZeroPoleResidueRectanglePipeline_source R)
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R

/-- The typed hom of the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_hom
    (R : ℝ) :
    TraceCorQHom
      (completedZetaZeroPoleResidueRectanglePipeline_source R)
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  completedZetaZeroPoleResidueRectangleTraceCorQHom R

/-- The explicit representative of the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_representative
    (R : ℝ) :
    TraceCorQHomRepresentative
      (completedZetaZeroPoleResidueRectanglePipeline_source R)
      completedZetaZeroPoleResidueRectanglePipeline_target :=
  completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R

/-- The ambient candidate of the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_candidate
    (R : ℝ) :
    TraceCorQQuotientCandidate :=
  completedZetaZeroPoleResidueRectangleTraceCorQCandidate R

/-- The ambient quotient class of the rectangle-certified zero-pole residue pipeline. -/
def completedZetaZeroPoleResidueRectanglePipeline_quotient
    (R : ℝ) :
    TraceCorQQuotient :=
  completedZetaZeroPoleResidueRectangleTraceCorQQuotient R

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

/-- The pipeline generator bookkeeping payload is the rectangle-certified generator payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_generator_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_generator R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQGenerator R).traceBookkeepingCount :=
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

/-- The pipeline typed term bookkeeping payload is the pipeline generator payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_term_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_term R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_generator R).traceBookkeepingCount :=
  rfl

/-- The pipeline formal sum imported payload is the upstream typed formal-sum payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_importedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).importedRectangleCount :=
  rfl

/-- The pipeline formal sum bookkeeping payload is the upstream typed formal-sum payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomFormalSum R).traceBookkeepingCount :=
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

/-- The pipeline hom is the class of the pipeline representative. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_hom_eq_ofRepresentative
    (R : ℝ) :
    completedZetaZeroPoleResidueRectanglePipeline_hom R =
      TraceCorQHom.ofRepresentative
        (completedZetaZeroPoleResidueRectanglePipeline_representative R) :=
  rfl

/-- The ambient image of the pipeline hom is the pipeline quotient. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_ambient
    (R : ℝ) :
    TraceCorQHom.ambient
      (completedZetaZeroPoleResidueRectanglePipeline_hom R) =
      completedZetaZeroPoleResidueRectanglePipeline_quotient R :=
  rfl

/-- The pipeline quotient is represented by the pipeline candidate. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_quotient_eq_ofCandidate
    (R : ℝ) :
    completedZetaZeroPoleResidueRectanglePipeline_quotient R =
      TraceCorQQuotient.ofCandidate
        (completedZetaZeroPoleResidueRectanglePipeline_candidate R) :=
  rfl

/-- The pipeline rectangle certificate ledger is the rectangle certificate ledger. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_rectangleCertificateLedger
    (R : ℝ) :
    completedZetaZeroPoleFiniteSquareRectangleCertificateLedger R =
      ResidueChannelCertificateLedger.ofExplicitFormulaRectangle
        (completedZetaZeroPoleResidueRectanglePipeline_rectangle R) :=
  rfl

/-- The pipeline representative has the upstream representative certificate ledger. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_representative_certificateLedger
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_representative R).certificateLedger =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R).certificateLedger :=
  rfl

/-- The pipeline representative imported payload is the upstream representative payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_representative_importedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_representative R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R).importedRectangleCount :=
  rfl

/-- The pipeline representative bookkeeping payload is the upstream representative payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_representative_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_representative R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R).traceBookkeepingCount :=
  rfl

/-- The pipeline representative imports formal-sum payload and empty relation-ledger payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_representative_importedRectangleCount_split
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_representative R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangleCount +
        TraceCorQRelationLedger.empty.importedRectangleCount :=
  completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative_importedRectangleCount R

/-- The pipeline representative keeps formal-sum bookkeeping and empty relation-ledger bookkeeping. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_representative_traceBookkeepingCount_split
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_representative R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).traceBookkeepingCount +
        TraceCorQRelationLedger.empty.traceBookkeepingCount :=
  completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative_traceBookkeepingCount R

/-- The pipeline candidate has the representative certificate ledger. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_candidate_certificateLedger
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R).certificateLedger =
      (completedZetaZeroPoleResidueRectanglePipeline_representative R).certificateLedger :=
  rfl

/-- The pipeline candidate carries the representative imported payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_candidate_importedRectangleCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_representative R).importedRectangleCount :=
  rfl

/-- The pipeline candidate carries the representative bookkeeping payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_candidate_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_representative R).traceBookkeepingCount :=
  rfl

/-- The pipeline candidate imports formal-sum payload and empty relation-ledger payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_candidate_importedRectangleCount_split
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangleCount +
        TraceCorQRelationLedger.empty.importedRectangleCount :=
  Eq.trans
    (completedZetaZeroPoleResidueRectanglePipeline_candidate_importedRectangleCount R)
    (completedZetaZeroPoleResidueRectanglePipeline_representative_importedRectangleCount_split R)

/-- The pipeline candidate keeps formal-sum bookkeeping and empty relation-ledger bookkeeping. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_candidate_traceBookkeepingCount_split
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).traceBookkeepingCount +
        TraceCorQRelationLedger.empty.traceBookkeepingCount :=
  Eq.trans
    (completedZetaZeroPoleResidueRectanglePipeline_candidate_traceBookkeepingCount R)
    (completedZetaZeroPoleResidueRectanglePipeline_representative_traceBookkeepingCount_split R)

/-- Positivity of `R` is positivity of the pipeline rectangle's recorded height. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_rectangle_positiveHeight
    {R : ℝ} (hR : 0 < R) :
    0 < (completedZetaZeroPoleResidueRectanglePipeline_rectangle R).T :=
  hR

/-- The pipeline is sound when the recorded rectangle height is positive. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_sound_of_rectangleHeight
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ}
    (hT : 0 < (completedZetaZeroPoleResidueRectanglePipeline_rectangle R).T) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleResidueRectangleTraceCorQTypedClass_sound_of_rectangleHeight
    f hPhi hT

/-- The pipeline is sound for any positive finite-square height `R`. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_sound
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R) :
    completedZetaZeroPoleFiniteSquareBoundaryTrace f R =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  completedZetaZeroPoleResidueRectanglePipeline_sound_of_rectangleHeight
    f
    hPhi
    (completedZetaZeroPoleResidueRectanglePipeline_rectangle_positiveHeight
      (R := R)
      hR)

end AnalyticMotives
end LFunctions
end Boundary
