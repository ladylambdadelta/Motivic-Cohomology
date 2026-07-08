import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Public.Projections.Owner

/-!
# Top-root quotient-candidate projection laws

This file exposes concrete quotient-candidate projection laws through the
top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes candidate certificate-ledger splitting. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_certificateLedger_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.certificateLedger =
      ResidueChannelCertificateLedger.append
        candidate.formalSum.certificateLedger
        candidate.ledger.certificateLedger :=
  TraceCorQ.quotientCandidate_certificateLedger_eq_formalSum_ledger
    candidate

/-- The top root exposes candidate imported-payload splitting. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_importedRectangleCount_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.importedRectangleCount =
      candidate.formalSum.importedRectangleCount +
        candidate.ledger.importedRectangleCount :=
  TraceCorQ.quotientCandidate_importedRectangleCount_eq_formalSum_ledger
    candidate

/-- The top root exposes candidate imported-rectangle splitting. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_importedRectangles_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.importedRectangles =
      candidate.formalSum.importedRectangles ++
        candidate.ledger.importedRectangles :=
  TraceCorQ.quotientCandidate_importedRectangles_eq_formalSum_ledger
    candidate

/-- The top root exposes candidate imported counts as list lengths. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_importedRectangleCount_eq_length
    (candidate : TraceCorQQuotientCandidate) :
    candidate.importedRectangleCount =
      candidate.importedRectangles.length :=
  TraceCorQ.quotientCandidate_importedRectangleCount_eq_length
    candidate

/-- The top root exposes candidate bookkeeping-payload splitting. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_traceBookkeepingCount_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.traceBookkeepingCount =
      candidate.formalSum.traceBookkeepingCount +
        candidate.ledger.traceBookkeepingCount :=
  TraceCorQ.quotientCandidate_traceBookkeepingCount_eq_formalSum_ledger
    candidate

/-- The top root exposes candidate rewrite-step splitting. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_rewriteStepCount_eq_formalSum_ledger
    (candidate : TraceCorQQuotientCandidate) :
    candidate.rewriteStepCount =
      candidate.formalSum.rewriteStepCount +
        candidate.ledger.rewriteStepCount :=
  TraceCorQ.quotientCandidate_rewriteStepCount_eq_formalSum_ledger
    candidate

/-- The top root exposes the input of an input-built candidate. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_ofInput_input
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).input =
      input :=
  TraceCorQ.quotientCandidate_ofInput_input
    input

/-- The top root exposes the empty candidate input. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_empty_input :
    TraceCorQQuotientCandidate.empty.input =
      TraceCorQQuotientInput.empty :=
  TraceCorQ.quotientCandidate_empty_input

/-- The top root exposes the formal sum of an input-built candidate. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_ofInput_formalSum
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).formalSum =
      input.formalSum :=
  TraceCorQ.quotientCandidate_ofInput_formalSum
    input

/-- The top root exposes the ledger of an input-built candidate. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_ofInput_ledger
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).ledger =
      input.ledger :=
  TraceCorQ.quotientCandidate_ofInput_ledger
    input

/-- The top root exposes the certificate ledger of an input-built candidate. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_ofInput_certificateLedger
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).certificateLedger =
      input.certificateLedger :=
  TraceCorQ.quotientCandidate_ofInput_certificateLedger
    input

/-- The top root exposes the imported count of an input-built candidate. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_ofInput_importedRectangleCount
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).importedRectangleCount =
      input.importedRectangleCount :=
  TraceCorQ.quotientCandidate_ofInput_importedRectangleCount
    input

/-- The top root exposes the imported rectangles of an input-built candidate. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_ofInput_importedRectangles
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).importedRectangles =
      input.importedRectangles :=
  TraceCorQ.quotientCandidate_ofInput_importedRectangles
    input

/-- The top root exposes the bookkeeping count of an input-built candidate. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_ofInput_traceBookkeepingCount
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).traceBookkeepingCount =
      input.traceBookkeepingCount :=
  TraceCorQ.quotientCandidate_ofInput_traceBookkeepingCount
    input

/-- The top root exposes the rewrite count of an input-built candidate. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_ofInput_rewriteStepCount
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).rewriteStepCount =
      input.rewriteStepCount :=
  TraceCorQ.quotientCandidate_ofInput_rewriteStepCount
    input

end AnalyticMotives
end LFunctions
end Boundary
