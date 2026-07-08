import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Owner

/-!
# Addition projections for quotient candidates

This file owns the projection and payload facts for addition of raw quotient
candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The input of a candidate sum is the sum of the inputs. -/
theorem TraceCorQQuotientCandidate.add_input
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).input =
      TraceCorQQuotientInput.add left.input right.input :=
  rfl

/-- The formal sum of a candidate sum is the sum of formal sums. -/
theorem TraceCorQQuotientCandidate.add_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).formalSum =
      TraceCorQFormalSum.add left.formalSum right.formalSum :=
  rfl

/-- The ledger of a candidate sum is the appended ledger. -/
theorem TraceCorQQuotientCandidate.add_ledger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  rfl

/-- The certificate ledger of a candidate sum records summed formal and relation certificates. -/
theorem TraceCorQQuotientCandidate.add_certificateLedger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.append
          left.formalSum.certificateLedger
          right.formalSum.certificateLedger)
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger) :=
  TraceCorQQuotientInput.add_certificateLedger
    left.input
    right.input

/-- Candidate addition adds imported finite-rectangle payload by component. -/
theorem TraceCorQQuotientCandidate.add_importedRectangleCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).importedRectangleCount =
      (left.formalSum.importedRectangleCount +
        right.formalSum.importedRectangleCount) +
        (left.ledger.importedRectangleCount +
          right.ledger.importedRectangleCount) :=
  TraceCorQQuotientInput.add_importedRectangleCount
    left.input
    right.input

/-- Candidate addition concatenates imported rectangle payload by component. -/
theorem TraceCorQQuotientCandidate.add_importedRectangles
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).importedRectangles =
      (left.formalSum.importedRectangles ++
        right.formalSum.importedRectangles) ++
        (left.ledger.importedRectangles ++
          right.ledger.importedRectangles) :=
  TraceCorQQuotientInput.add_importedRectangles
    left.input
    right.input

/-- Candidate addition adds internal trace-bookkeeping payload by component. -/
theorem TraceCorQQuotientCandidate.add_traceBookkeepingCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).traceBookkeepingCount =
      (left.formalSum.traceBookkeepingCount +
        right.formalSum.traceBookkeepingCount) +
        (left.ledger.traceBookkeepingCount +
          right.ledger.traceBookkeepingCount) :=
  TraceCorQQuotientInput.add_traceBookkeepingCount
    left.input
    right.input

/-- Candidate addition adds explicit rewrite-step payload by component. -/
theorem TraceCorQQuotientCandidate.add_rewriteStepCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).rewriteStepCount =
      (left.formalSum.rewriteStepCount +
        right.formalSum.rewriteStepCount) +
        (left.ledger.rewriteStepCount +
          right.ledger.rewriteStepCount) :=
  TraceCorQQuotientInput.add_rewriteStepCount
    left.input
    right.input

end AnalyticMotives
end LFunctions
end Boundary
