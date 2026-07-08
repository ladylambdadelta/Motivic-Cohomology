import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Owner

/-!
# Scalar projection facts for quotient candidates

This file owns the basic projection and payload facts for scalar multiplication
of raw quotient candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The input of a scaled candidate is the scaled input. -/
theorem TraceCorQQuotientCandidate.smul_input
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).input =
      TraceCorQQuotientInput.smul coefficient candidate.input :=
  rfl

/-- The formal sum of a scaled candidate is the scaled formal sum. -/
theorem TraceCorQQuotientCandidate.smul_formalSum
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).formalSum =
      TraceCorQFormalSum.smul coefficient candidate.formalSum :=
  rfl

/-- Scaling a candidate preserves its relation ledger. -/
theorem TraceCorQQuotientCandidate.smul_ledger
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).ledger =
      candidate.ledger :=
  rfl

/-- Scaling a candidate preserves its analytic certificate ledger. -/
theorem TraceCorQQuotientCandidate.smul_certificateLedger
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).certificateLedger =
      candidate.certificateLedger :=
  TraceCorQQuotientInput.smul_certificateLedger
    coefficient
    candidate.input

/-- Scaling a candidate preserves imported finite-rectangle payload. -/
theorem TraceCorQQuotientCandidate.smul_importedRectangleCount
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).importedRectangleCount =
      candidate.importedRectangleCount :=
  TraceCorQQuotientInput.smul_importedRectangleCount
    coefficient
    candidate.input

/-- Scaling a candidate preserves imported finite explicit-formula rectangles. -/
theorem TraceCorQQuotientCandidate.smul_importedRectangles
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).importedRectangles =
      candidate.importedRectangles :=
  TraceCorQQuotientInput.smul_importedRectangles
    coefficient
    candidate.input

/-- Scaling a candidate preserves internal trace-bookkeeping payload. -/
theorem TraceCorQQuotientCandidate.smul_traceBookkeepingCount
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).traceBookkeepingCount =
      candidate.traceBookkeepingCount :=
  TraceCorQQuotientInput.smul_traceBookkeepingCount
    coefficient
    candidate.input

/-- Scaling a candidate preserves explicit rewrite-step payload. -/
theorem TraceCorQQuotientCandidate.smul_rewriteStepCount
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).rewriteStepCount =
      candidate.rewriteStepCount :=
  TraceCorQQuotientInput.smul_rewriteStepCount
    coefficient
    candidate.input

end AnalyticMotives
end LFunctions
end Boundary
