import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Projections.Owner

/-!
# Public quotient-candidate projection laws

This file exposes concrete quotient-candidate projection laws under the
`TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes candidate certificate-ledger splitting. -/
theorem TraceCorQ.quotientCandidate_certificateLedger_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.certificateLedger =
      ResidueChannelCertificateLedger.append
        candidate.formalSum.certificateLedger
        candidate.ledger.certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    candidate

/-- The trace-correspondence root exposes candidate imported-payload splitting. -/
theorem TraceCorQ.quotientCandidate_importedRectangleCount_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.importedRectangleCount =
      candidate.formalSum.importedRectangleCount +
        candidate.ledger.importedRectangleCount :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_formalSum_ledger
    candidate

/-- The trace-correspondence root exposes candidate imported-rectangle splitting. -/
theorem TraceCorQ.quotientCandidate_importedRectangles_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.importedRectangles =
      candidate.formalSum.importedRectangles ++
        candidate.ledger.importedRectangles :=
  TraceCorQQuotientCandidate.importedRectangles_eq_formalSum_ledger
    candidate

/-- The trace-correspondence root exposes candidate imported counts as list lengths. -/
theorem TraceCorQ.quotientCandidate_importedRectangleCount_eq_length
    (candidate : TraceCorQQuotientCandidate) :
    candidate.importedRectangleCount =
      candidate.importedRectangles.length :=
  TraceCorQQuotientCandidate.importedRectangleCount_eq_length_importedRectangles
    candidate

/-- The trace-correspondence root exposes candidate bookkeeping-payload splitting. -/
theorem TraceCorQ.quotientCandidate_traceBookkeepingCount_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.traceBookkeepingCount =
      candidate.formalSum.traceBookkeepingCount +
        candidate.ledger.traceBookkeepingCount :=
  TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    candidate

/-- The trace-correspondence root exposes candidate rewrite-step splitting. -/
theorem TraceCorQ.quotientCandidate_rewriteStepCount_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.rewriteStepCount =
      candidate.formalSum.rewriteStepCount +
        candidate.ledger.rewriteStepCount :=
  TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    candidate

/-- The trace-correspondence root exposes the input of an input-built candidate. -/
theorem TraceCorQ.quotientCandidate_ofInput_input
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).input =
      input :=
  TraceCorQQuotientCandidate.ofInput_input
    input

/-- The trace-correspondence root exposes the empty candidate input. -/
theorem TraceCorQ.quotientCandidate_empty_input :
    TraceCorQQuotientCandidate.empty.input =
      TraceCorQQuotientInput.empty :=
  TraceCorQQuotientCandidate.empty_input

/-- The trace-correspondence root exposes the formal sum of an input-built candidate. -/
theorem TraceCorQ.quotientCandidate_ofInput_formalSum
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).formalSum =
      input.formalSum :=
  TraceCorQQuotientCandidate.ofInput_formalSum
    input

/-- The trace-correspondence root exposes the ledger of an input-built candidate. -/
theorem TraceCorQ.quotientCandidate_ofInput_ledger
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).ledger =
      input.ledger :=
  TraceCorQQuotientCandidate.ofInput_ledger
    input

/-- The trace-correspondence root exposes the certificate ledger of an input-built candidate. -/
theorem TraceCorQ.quotientCandidate_ofInput_certificateLedger
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).certificateLedger =
      input.certificateLedger :=
  TraceCorQQuotientCandidate.ofInput_certificateLedger
    input

/-- The trace-correspondence root exposes the imported count of an input-built candidate. -/
theorem TraceCorQ.quotientCandidate_ofInput_importedRectangleCount
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).importedRectangleCount =
      input.importedRectangleCount :=
  TraceCorQQuotientCandidate.ofInput_importedRectangleCount
    input

/-- The trace-correspondence root exposes the imported rectangles of an input-built candidate. -/
theorem TraceCorQ.quotientCandidate_ofInput_importedRectangles
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).importedRectangles =
      input.importedRectangles :=
  TraceCorQQuotientCandidate.ofInput_importedRectangles
    input

/-- The trace-correspondence root exposes the bookkeeping count of an input-built candidate. -/
theorem TraceCorQ.quotientCandidate_ofInput_traceBookkeepingCount
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).traceBookkeepingCount =
      input.traceBookkeepingCount :=
  TraceCorQQuotientCandidate.ofInput_traceBookkeepingCount
    input

/-- The trace-correspondence root exposes the rewrite count of an input-built candidate. -/
theorem TraceCorQ.quotientCandidate_ofInput_rewriteStepCount
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).rewriteStepCount =
      input.rewriteStepCount :=
  TraceCorQQuotientCandidate.ofInput_rewriteStepCount
    input

end AnalyticMotives
end LFunctions
end Boundary
