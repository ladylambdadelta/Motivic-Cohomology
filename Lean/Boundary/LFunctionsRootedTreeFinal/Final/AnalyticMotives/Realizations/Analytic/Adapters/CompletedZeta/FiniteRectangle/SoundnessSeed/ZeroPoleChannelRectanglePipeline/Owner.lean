import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectanglePipeline.TransportPayload.Owner

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

/-- The pipeline generator rectangle list is the scheduled-rectangle generator rectangle list. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_generator_importedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
      f F h u).importedRectangles =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).importedRectangles :=
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

/-- The pipeline generator rewrite-step payload is the scheduled-rectangle generator payload. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_generator_rewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQGenerator
        f F h u).rewriteStepCount :=
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

/-- The pipeline typed term rectangle list is the pipeline generator rectangle list. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_term_importedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
      f F h u).importedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
        f F h u).importedRectangles :=
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

/-- The pipeline typed term rewrite-step payload is the pipeline generator payload. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_term_rewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
        f F h u).rewriteStepCount :=
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

/-- The pipeline formal sum rectangle list is the upstream typed formal-sum rectangle list. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_importedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u).importedRectangles =
      (completedZetaZeroPoleChannelScheduledRectangleTraceCorQHomFormalSum
        f F h u).importedRectangles :=
  rfl

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

/-- The pipeline formal sum exposes the rectangle list carried by its term. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_importedRectangles_eq_term
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u).importedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
        f F h u).importedRectangles ++
        ResidueChannelCertificateLedger.empty.importedRectangles :=
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

/-- The pipeline formal sum carries generator rewrite steps plus zero. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_rewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
        f F h u).rewriteStepCount +
        0 :=
  completedZetaZeroPoleChannelScheduledRectangleTraceCorQFormalSum_rewriteStepCount
    f F h u

/-- The pipeline formal sum carries term rewrite steps plus zero. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_rewriteStepCount_eq_term
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
        f F h u).rewriteStepCount +
        0 :=
  rfl

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
