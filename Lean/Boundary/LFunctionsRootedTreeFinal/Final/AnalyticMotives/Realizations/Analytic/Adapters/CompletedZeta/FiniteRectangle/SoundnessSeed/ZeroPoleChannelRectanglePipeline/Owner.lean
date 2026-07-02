import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectangleTypedClass.Owner

/-!
# Zero-pole scheduled-rectangle channel pipeline

This file collects the end-to-end data for the scheduled-rectangle channel
trace correspondence.

It does not introduce new structure.  Each declaration is a named projection
of the concrete scheduled rectangle, certified presentation, transport,
generator, typed hom, representative, candidate, and quotient already
constructed upstream.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The scheduled rectangle certificate used by the zero-pole channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangle
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  completedZetaZeroPoleScheduledChannelRectangle f F h u

/-- The source presentation of the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_source
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQObject :=
  completedZetaZeroPoleChannelScheduledRectangleHomSource f F h u

/-- The target presentation of the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_target :
    TraceCorQObject :=
  completedZetaZeroPoleChannelScheduledRectangleHomTarget

/-- The transport used by the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceTransport :=
  completedZetaZeroPoleChannelTransportWithScheduledRectangle f F h u

/-- The generator used by the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQGenerator :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator f F h u

/-- The typed term used by the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_term
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHomTerm
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u)
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm
    f F h u

/-- The typed singleton formal sum used by the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHomFormalSum
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u)
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
    f F h u

/-- The typed hom of the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_hom
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHom
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u)
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHom f F h u

/-- The explicit representative of the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHomRepresentative
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u)
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative
    f F h u

/-- The ambient candidate of the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQQuotientCandidate :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate f F h u

/-- The ambient quotient class of the scheduled-rectangle channel pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_quotient
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQQuotient :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQQuotient f F h u

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

/-- The rectangle ledger used by the pipeline. -/
def completedZetaZeroPoleChannelScheduledRectanglePipeline_rectangleLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ResidueChannelCertificateLedger :=
  completedZetaZeroPoleScheduledChannelRectangleCertificateLedger
    f F h u

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

/-- The pipeline generator starts at the pipeline source. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_generator_source
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
      f F h u).source =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u :=
  rfl

/-- The pipeline generator targets the pipeline target. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_generator_target
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
      f F h u).target =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target :=
  rfl

/-- The pipeline generator carries the zero-pole channel path. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_generator_path
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
      f F h u).path =
      completedZetaZeroPoleChannelPath :=
  rfl

/-- The pipeline generator path starts at the source presentation expression. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_generator_path_source
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
      f F h u).path.source =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).source :=
  (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
    f F h u).path_source

/-- The pipeline generator path targets the target presentation expression. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_generator_path_target
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
      f F h u).path.target =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_target.source :=
  (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
    f F h u).path_target

/-- The pipeline generator carries the scheduled-rectangle channel generator ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_generator_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
      f F h u).certificateLedger =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).certificateLedger :=
  rfl

/-- The pipeline generator imported payload is the scheduled-rectangle generator payload. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_generator_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).importedRectangleCount :=
  rfl

/-- The pipeline generator bookkeeping payload is the scheduled-rectangle generator payload. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_generator_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).traceBookkeepingCount :=
  rfl

/-- The pipeline typed term has coefficient one. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_term_coefficient
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
      f F h u).coefficient =
      1 :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm_coefficient
    f F h u

/-- The pipeline typed term has the pipeline generator. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_term_generator
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
      f F h u).generator =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
        f F h u :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomTerm_generator
    f F h u

/-- The pipeline typed term carries the pipeline generator ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_term_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
      f F h u).certificateLedger =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
        f F h u).certificateLedger :=
  rfl

/-- The pipeline typed term imported payload is the pipeline generator payload. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_term_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
        f F h u).importedRectangleCount :=
  rfl

/-- The pipeline typed term bookkeeping payload is the pipeline generator payload. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_term_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
        f F h u).traceBookkeepingCount :=
  rfl

/-- The pipeline formal sum is the typed singleton already constructed upstream. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u =
      completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
        f F h u :=
  rfl

/-- The pipeline formal sum is the singleton list containing the pipeline typed term. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_eq_singleton_term
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u =
      [completedZetaZeroPoleChannelScheduledRectanglePipeline_term f F h u] :=
  rfl

/-- Forgetting endpoint proofs recovers the raw scheduled singleton. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_raw
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u).raw =
      completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
        f F h u :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_raw
    f F h u

/-- The pipeline formal sum carries the raw scheduled singleton certificate ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u).certificateLedger =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum
        f F h u).certificateLedger :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum_certificateLedger
    f F h u

/-- The pipeline formal sum records the pipeline term ledger followed by the empty ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_certificateLedger_eq_term
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u).certificateLedger =
      ResidueChannelCertificateLedger.append
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
          f F h u).certificateLedger
        ResidueChannelCertificateLedger.empty :=
  rfl

/-- The pipeline formal sum imports the generator payload plus zero. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
        f F h u).importedRectangleCount +
        0 :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum_importedRectangleCount
    f F h u

/-- The pipeline formal sum imports the term payload plus zero. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_importedRectangleCount_eq_term
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
        f F h u).importedRectangleCount +
        0 :=
  rfl

/-- The pipeline formal sum carries generator bookkeeping plus zero. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
        f F h u).traceBookkeepingCount +
        0 :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum_traceBookkeepingCount
    f F h u

/-- The pipeline formal sum carries term bookkeeping plus zero. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_traceBookkeepingCount_eq_term
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
        f F h u).traceBookkeepingCount +
        0 :=
  rfl

/-- The pipeline hom is the class of the pipeline representative. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_hom_eq_ofRepresentative
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u =
      TraceCorQHom.ofRepresentative
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
          f F h u) :=
  rfl

/-- The ambient image of the pipeline hom is the pipeline quotient. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_ambient
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    TraceCorQHom.ambient
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_hom f F h u) =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_quotient
        f F h u :=
  rfl

/-- The pipeline quotient is represented by the pipeline candidate. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_quotient_eq_ofCandidate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleChannelScheduledRectanglePipeline_quotient
      f F h u =
      TraceCorQQuotient.ofCandidate
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
          f F h u) :=
  rfl

/-- The pipeline representative has the pipeline formal sum. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_representative_formalSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
      f F h u).formalSum =
      completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u :=
  rfl

/-- The pipeline representative has the empty relation ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_representative_ledger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
      f F h u).ledger =
      TraceCorQRelationLedger.empty :=
  rfl

/-- The pipeline representative records formal-sum certificates plus the empty relation ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_representative_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
      f F h u).certificateLedger =
      ResidueChannelCertificateLedger.append
        (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
          f F h u).certificateLedger
        TraceCorQRelationLedger.empty.certificateLedger :=
  rfl

/-- The pipeline representative imported payload splits into formal-sum and empty-ledger payload. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_representative_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).importedRectangleCount +
        TraceCorQRelationLedger.empty.importedRectangleCount :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative_importedRectangleCount
    f F h u

/-- The pipeline representative bookkeeping splits into formal-sum and empty-ledger payload. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_representative_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).traceBookkeepingCount +
        TraceCorQRelationLedger.empty.traceBookkeepingCount :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomRepresentative_traceBookkeepingCount
    f F h u

/-- The pipeline candidate has the representative's certificate ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_certificateLedger
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
      f F h u).certificateLedger =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
        f F h u).certificateLedger :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQCandidate_certificateLedger
    f F h u

/-- The pipeline candidate imported payload is the representative imported payload. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_importedRectangleCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
        f F h u).importedRectangleCount :=
  rfl

/-- The pipeline candidate bookkeeping payload is the representative bookkeeping payload. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_traceBookkeepingCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
        f F h u).traceBookkeepingCount :=
  rfl

/-- The pipeline candidate imports formal-sum payload and empty relation-ledger payload. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_importedRectangleCount_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).importedRectangleCount +
        TraceCorQRelationLedger.empty.importedRectangleCount :=
  Eq.trans
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_importedRectangleCount
      f F h u)
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative_importedRectangleCount
      f F h u)

/-- The pipeline candidate keeps formal-sum bookkeeping and empty relation-ledger bookkeeping. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_traceBookkeepingCount_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
      f F h u).traceBookkeepingCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).traceBookkeepingCount +
        TraceCorQRelationLedger.empty.traceBookkeepingCount :=
  Eq.trans
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_traceBookkeepingCount
      f F h u)
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative_traceBookkeepingCount
      f F h u)

/-- The pipeline is sound at its scheduled rectangle parameter. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_sound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    completedZetaZeroPoleLeftVerticalTrace f F h u =
      completedZetaZeroPoleRightVerticalTrace f F h u +
        completedZetaZeroPoleHorizontalTrace f F h u -
        completedZetaZeroPoleRectangleBoundaryTrace f F h u :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQTypedClass_sound
    f F h u

end AnalyticMotives
end LFunctions
end Boundary
