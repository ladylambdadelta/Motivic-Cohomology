import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRectanglePipeline.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleChannelRectanglePipeline.Quotient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRelationWitness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Certificates.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Payload.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Owner

/-!
# Completed-zeta finite-rectangle payload length facts

This file records imported-rectangle count-equals-list-length facts for the two
completed-zeta zero-pole rectangle-certified pipelines.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The residue rectangle pipeline source count is the length of its rectangle list. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_source_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_source R).importedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleResidueRectanglePipeline_source R)

/-- The residue rectangle pipeline transport count is the length of its rectangle list. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_transport_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_transport R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_transport R).importedRectangles.length :=
  TraceTransport.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleResidueRectanglePipeline_transport R)

/-- The residue rectangle pipeline generator count is the length of its rectangle list. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_generator_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_generator R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_generator R).importedRectangles.length :=
  TraceCorQGenerator.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleResidueRectanglePipeline_generator R)

/-- The residue rectangle pipeline typed term count is the length of its rectangle list. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_term_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_term R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_term R).importedRectangles.length :=
  TraceCorQHomTerm.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleResidueRectanglePipeline_term R)

/-- The residue rectangle pipeline formal-sum count is the length of its rectangle list. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_formalSum_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_formalSum R).importedRectangles.length :=
  TraceCorQHomFormalSum.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleResidueRectanglePipeline_formalSum R)

/-- The residue rectangle pipeline representative count is the length of its rectangle list. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_representative_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_representative R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_representative R).importedRectangles.length :=
  TraceCorQHomRepresentative.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleResidueRectanglePipeline_representative R)

/-- The residue rectangle pipeline candidate count is the length of its rectangle list. -/
theorem completedZetaZeroPoleResidueRectanglePipeline_candidate_importedRectangleCount_eq_length
    (R : ℝ) :
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R).importedRectangleCount =
      (completedZetaZeroPoleResidueRectanglePipeline_candidate R).importedRectangles.length :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleResidueRectanglePipeline_candidate R)

/-- The channel rectangle pipeline source count is the length of its rectangle list. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_source_importedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_source
        f F h u).importedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_source f F h u)

/-- The channel rectangle pipeline transport count is the length of its rectangle list. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_transport_importedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport
        f F h u).importedRectangles.length :=
  TraceTransport.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_transport f F h u)

/-- The channel rectangle pipeline generator count is the length of its rectangle list. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_generator_importedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator
        f F h u).importedRectangles.length :=
  TraceCorQGenerator.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_generator f F h u)

/-- The channel rectangle pipeline typed term count is the length of its rectangle list. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_term_importedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_term
        f F h u).importedRectangles.length :=
  TraceCorQHomTerm.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_term f F h u)

/-- The channel rectangle pipeline formal-sum count is the length of its rectangle list. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum_importedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum
        f F h u).importedRectangles.length :=
  TraceCorQHomFormalSum.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_formalSum f F h u)

/-- The channel rectangle pipeline representative count is the length of its rectangle list. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_representative_importedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative
        f F h u).importedRectangles.length :=
  TraceCorQHomRepresentative.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_representative f F h u)

/-- The channel rectangle pipeline candidate count is the length of its rectangle list. -/
theorem completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate_importedRectangleCount_eq_length
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
      f F h u).importedRectangleCount =
      (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate
        f F h u).importedRectangles.length :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (completedZetaZeroPoleChannelScheduledRectanglePipeline_candidate f F h u)

/-- The zero-pole quotient input count is the length of its rectangle list. -/
theorem completedZetaZeroPoleTraceCorQQuotientInput_importedRectangleCount_eq_length :
    completedZetaZeroPoleTraceCorQQuotientInput.importedRectangleCount =
      completedZetaZeroPoleTraceCorQQuotientInput.importedRectangles.length :=
  TraceCorQQuotientInput.importedRectangleCount_eq_length_importedRectangles
    completedZetaZeroPoleTraceCorQQuotientInput

/-- The zero-pole quotient candidate count is the length of its rectangle list. -/
theorem completedZetaZeroPoleTraceCorQQuotientCandidate_importedRectangleCount_eq_length :
    completedZetaZeroPoleTraceCorQQuotientCandidate.importedRectangleCount =
      completedZetaZeroPoleTraceCorQQuotientCandidate.importedRectangles.length :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    completedZetaZeroPoleTraceCorQQuotientCandidate

/-- The zero-pole relation support candidate count is the length of its rectangle list. -/
theorem completedZetaZeroPoleRelationSupportCandidate_importedRectangleCount_eq_length :
    completedZetaZeroPoleRelationSupportCandidate.importedRectangleCount =
      completedZetaZeroPoleRelationSupportCandidate.importedRectangles.length :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    completedZetaZeroPoleRelationSupportCandidate

/-- The zero-pole relation support witness count is the length of its rectangle list. -/
theorem completedZetaZeroPoleRelationSupportWitness_importedRectangleCount_eq_length :
    completedZetaZeroPoleRelationSupportWitness.importedRectangleCount =
      completedZetaZeroPoleRelationSupportWitness.importedRectangles.length :=
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    completedZetaZeroPoleRelationSupportWitness

/-- The transported zero-pole support witness count is the length of its rectangle list. -/
theorem completedZetaZeroPoleQuotientCandidateSupportWitness_importedRectangleCount_eq_length :
    completedZetaZeroPoleQuotientCandidateSupportWitness.importedRectangleCount =
      completedZetaZeroPoleQuotientCandidateSupportWitness.importedRectangles.length :=
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    completedZetaZeroPoleQuotientCandidateSupportWitness

end AnalyticMotives
end LFunctions
end Boundary
