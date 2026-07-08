import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectanglePipeline.Owner

/-!
# Quotient projections for the zero-pole channel rectangle pipeline

This file owns the representative, candidate, and quotient projection facts
for the scheduled-rectangle channel pipeline.  The base pipeline owner keeps
the analytic rectangle, transport, generator, term, formal-sum payload, and
soundness theorem.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

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

/-- The pipeline representative rectangle list is formal-sum rectangles then empty-ledger rectangles. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_representative_importedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
      f F h u).importedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).importedRectangles ++
        TraceCorQRelationLedger.empty.importedRectangles :=
  TraceCorQHomRepresentative.importedRectangles_eq
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
      f F h u)

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

/-- The pipeline representative rewrite-step payload splits into formal sum and empty ledger. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_representative_rewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).rewriteStepCount +
        TraceCorQRelationLedger.empty.rewriteStepCount :=
  TraceCorQHomRepresentative.rewriteStepCount_eq
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
      f F h u)

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

/-- The pipeline candidate rectangle list is the representative rectangle list. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_importedRectangles
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
      f F h u).importedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
        f F h u).importedRectangles :=
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

/-- The pipeline candidate rewrite-step payload is the representative rewrite-step payload. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_rewriteStepCount
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
        f F h u).rewriteStepCount :=
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

/-- The pipeline candidate exposes formal-sum rectangles and empty relation-ledger rectangles. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_importedRectangles_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
      f F h u).importedRectangles =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).importedRectangles ++
        TraceCorQRelationLedger.empty.importedRectangles :=
  Eq.trans
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_importedRectangles
      f F h u)
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative_importedRectangles
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

/-- The pipeline candidate keeps formal-sum rewrite steps and empty relation-ledger steps. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_rewriteStepCount_split
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
      f F h u).rewriteStepCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).rewriteStepCount +
        TraceCorQRelationLedger.empty.rewriteStepCount :=
  Eq.trans
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_rewriteStepCount
      f F h u)
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative_rewriteStepCount
      f F h u)

end AnalyticMotives
end LFunctions
end Boundary
