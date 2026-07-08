import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRectanglePipeline.GeneratorFormalSum.Owner

/-!
# Zero-pole rectangle-certified pipeline

This file collects the hom, representative, candidate, quotient, and soundness
facts for the first rectangle-certified completed-zeta residue trace
correspondence.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

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

/-- The pipeline representative rectangle list is formal-sum rectangles then empty-ledger rectangles. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_representative_importedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_representative R).importedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangles ++
        TraceCorQRelationLedger.empty.importedRectangles :=
  TraceCorQHomRepresentative.importedRectangles_eq
    (completedZetaZeroPoleResidueRectanglePipeline_representative R)

/-- The pipeline representative bookkeeping payload is the upstream representative payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_representative_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_representative R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectangleTraceCorQHomRepresentative R).traceBookkeepingCount :=
  rfl

/-- The pipeline representative rewrite-step payload is the upstream representative payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_representative_rewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_representative R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).rewriteStepCount +
        TraceCorQRelationLedger.empty.rewriteStepCount :=
  TraceCorQHomRepresentative.rewriteStepCount_eq
    (completedZetaZeroPoleResidueRectanglePipeline_representative R)

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

/-- The pipeline candidate rectangle list is the representative rectangle list. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_candidate_importedRectangles
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R).importedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_representative R).importedRectangles :=
  rfl

/-- The pipeline candidate carries the representative bookkeeping payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_candidate_traceBookkeepingCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_representative R).traceBookkeepingCount :=
  rfl

/-- The pipeline candidate carries the representative rewrite-step payload. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_candidate_rewriteStepCount
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_representative R).rewriteStepCount :=
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

/-- The pipeline candidate exposes formal-sum rectangles and empty relation-ledger rectangles. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_candidate_importedRectangles_split
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R).importedRectangles =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangles ++
        TraceCorQRelationLedger.empty.importedRectangles :=
  Eq.trans
    (completedZetaZeroPoleResidueRectanglePipeline_candidate_importedRectangles R)
    (completedZetaZeroPoleResidueRectanglePipeline_representative_importedRectangles R)

/-- The pipeline candidate keeps formal-sum bookkeeping and empty relation-ledger bookkeeping. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_candidate_traceBookkeepingCount_split
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R).traceBookkeepingCount =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).traceBookkeepingCount +
        TraceCorQRelationLedger.empty.traceBookkeepingCount :=
  Eq.trans
    (completedZetaZeroPoleResidueRectanglePipeline_candidate_traceBookkeepingCount R)
    (completedZetaZeroPoleResidueRectanglePipeline_representative_traceBookkeepingCount_split R)

/-- The pipeline candidate keeps formal-sum rewrite steps and empty relation-ledger steps. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_candidate_rewriteStepCount_split
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R).rewriteStepCount =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).rewriteStepCount +
        TraceCorQRelationLedger.empty.rewriteStepCount :=
  Eq.trans
    (completedZetaZeroPoleResidueRectanglePipeline_candidate_rewriteStepCount R)
    (completedZetaZeroPoleResidueRectanglePipeline_representative_rewriteStepCount R)

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
