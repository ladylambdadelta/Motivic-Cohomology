import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Owner

/-!
# Projection facts for quotient candidates

This file owns payload splitting and input-projection facts for raw quotient
candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A candidate certificate ledger is formal-sum certificates followed by relation certificates. -/
theorem TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.certificateLedger =
      ResidueChannelCertificateLedger.append
        candidate.formalSum.certificateLedger
        candidate.ledger.certificateLedger :=
  TraceCorQQuotientInput.certificateLedger_eq_formalSum_ledger
    candidate.input

/-- A candidate imported payload splits into formal-sum and relation-ledger payload. -/
theorem TraceCorQQuotientCandidate.importedRectangleCount_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.importedRectangleCount =
      candidate.formalSum.importedRectangleCount +
        candidate.ledger.importedRectangleCount :=
  TraceCorQQuotientInput.importedRectangleCount_eq_formalSum_ledger
    candidate.input

/-- Candidate imported rectangles split into formal-sum and relation-ledger rectangles. -/
theorem TraceCorQQuotientCandidate.importedRectangles_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.importedRectangles =
      candidate.formalSum.importedRectangles ++
        candidate.ledger.importedRectangles :=
  TraceCorQQuotientInput.importedRectangles_eq_formalSum_ledger
    candidate.input

/-- Candidate imported-rectangle count is the length of its rectangle list. -/
theorem TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    (candidate : TraceCorQQuotientCandidate) :
    candidate.importedRectangleCount =
      candidate.importedRectangles.length :=
  TraceCorQQuotientInput.importedRectangleCount_eq_length_importedRectangles
    candidate.input

/-- A candidate bookkeeping payload splits into formal-sum and relation-ledger payload. -/
theorem TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.traceBookkeepingCount =
      candidate.formalSum.traceBookkeepingCount +
        candidate.ledger.traceBookkeepingCount :=
  TraceCorQQuotientInput.traceBookkeepingCount_eq_formalSum_ledger
    candidate.input

/-- A candidate rewrite-step payload splits into formal-sum and relation-ledger payload. -/
theorem TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.rewriteStepCount =
      candidate.formalSum.rewriteStepCount +
        candidate.ledger.rewriteStepCount :=
  TraceCorQQuotientInput.rewriteStepCount_eq_formalSum_ledger
    candidate.input

/-- Building a candidate from an input has that input. -/
theorem TraceCorQQuotientCandidate.ofInput_input
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).input =
      input :=
  rfl

/-- The empty candidate has empty input. -/
theorem TraceCorQQuotientCandidate.empty_input :
    TraceCorQQuotientCandidate.empty.input =
      TraceCorQQuotientInput.empty :=
  rfl

/-- The formal sum of a candidate built from an input is the input formal sum. -/
theorem TraceCorQQuotientCandidate.ofInput_formalSum
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).formalSum =
      input.formalSum :=
  rfl

/-- The ledger of a candidate built from an input is the input ledger. -/
theorem TraceCorQQuotientCandidate.ofInput_ledger
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).ledger =
      input.ledger :=
  rfl

/-- The certificate ledger of a candidate built from an input is the input certificate ledger. -/
theorem TraceCorQQuotientCandidate.ofInput_certificateLedger
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).certificateLedger =
      input.certificateLedger :=
  rfl

/-- The imported payload of a candidate built from an input is the input payload. -/
theorem TraceCorQQuotientCandidate.ofInput_importedRectangleCount
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).importedRectangleCount =
      input.importedRectangleCount :=
  rfl

/-- The imported rectangles of a candidate built from an input are the input rectangles. -/
theorem TraceCorQQuotientCandidate.ofInput_importedRectangles
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).importedRectangles =
      input.importedRectangles :=
  rfl

/-- The bookkeeping payload of a candidate built from an input is the input payload. -/
theorem TraceCorQQuotientCandidate.ofInput_traceBookkeepingCount
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).traceBookkeepingCount =
      input.traceBookkeepingCount :=
  rfl

/-- The rewrite-step payload of a candidate built from an input is the input payload. -/
theorem TraceCorQQuotientCandidate.ofInput_rewriteStepCount
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).rewriteStepCount =
      input.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
