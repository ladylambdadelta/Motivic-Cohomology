import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Composition.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Owner

/-!
# Composition facts for quotient candidates

This file owns the direct projections and payload decompositions for composing
raw quotient candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The input of a candidate composition is the composition of inputs. -/
theorem TraceCorQQuotientCandidate.comp_input
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).input =
      TraceCorQQuotientInput.comp left.input right.input :=
  rfl

/-- The formal sum of a candidate composition is the composed formal sum. -/
theorem TraceCorQQuotientCandidate.comp_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).formalSum =
      TraceCorQFormalSum.comp left.formalSum right.formalSum :=
  rfl

/-- The ledger of a candidate composition is the appended ledger. -/
theorem TraceCorQQuotientCandidate.comp_ledger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  rfl

/-- The certificate ledger of candidate composition records composed formal and relation certificates. -/
theorem TraceCorQQuotientCandidate.comp_certificateLedger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCorQFormalSum.comp left.formalSum right.formalSum).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger) :=
  TraceCorQQuotientInput.comp_certificateLedger
    left.input
    right.input

/-- Candidate composition splits imported payload into composed formal and relation parts. -/
theorem TraceCorQQuotientCandidate.comp_importedRectangleCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).importedRectangleCount =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).importedRectangleCount +
        (left.ledger.importedRectangleCount +
          right.ledger.importedRectangleCount) :=
  TraceCorQQuotientInput.comp_importedRectangleCount
    left.input
    right.input

/-- Candidate composition splits imported rectangles into composed formal and relation parts. -/
theorem TraceCorQQuotientCandidate.comp_importedRectangles
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).importedRectangles =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).importedRectangles ++
        (left.ledger.importedRectangles ++
          right.ledger.importedRectangles) :=
  TraceCorQQuotientInput.comp_importedRectangles
    left.input
    right.input

/-- Candidate composition splits bookkeeping payload into composed formal and relation parts. -/
theorem TraceCorQQuotientCandidate.comp_traceBookkeepingCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).traceBookkeepingCount =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).traceBookkeepingCount +
        (left.ledger.traceBookkeepingCount +
          right.ledger.traceBookkeepingCount) :=
  TraceCorQQuotientInput.comp_traceBookkeepingCount
    left.input
    right.input

/-- Candidate composition splits rewrite-step payload into composed formal and relation parts. -/
theorem TraceCorQQuotientCandidate.comp_rewriteStepCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).rewriteStepCount =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).rewriteStepCount +
        (left.ledger.rewriteStepCount +
          right.ledger.rewriteStepCount) :=
  TraceCorQQuotientInput.comp_rewriteStepCount
    left.input
    right.input

/-- Candidate composition with the empty candidate on the right exposes only the left ledger payload. -/
theorem TraceCorQQuotientCandidate.comp_empty_rewriteStepCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      candidate
      TraceCorQQuotientCandidate.empty).rewriteStepCount =
      0 +
        (candidate.ledger.rewriteStepCount +
          TraceCorQRelationLedger.empty.rewriteStepCount) :=
  TraceCorQQuotientInput.comp_empty_rewriteStepCount candidate.input

/-- Candidate composition with the empty candidate on the right exposes only imported ledger payload. -/
theorem TraceCorQQuotientCandidate.comp_empty_importedRectangleCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      candidate
      TraceCorQQuotientCandidate.empty).importedRectangleCount =
      0 +
        (candidate.ledger.importedRectangleCount +
          TraceCorQRelationLedger.empty.importedRectangleCount) :=
  TraceCorQQuotientInput.comp_empty_importedRectangleCount candidate.input

/-- Candidate composition with the empty candidate on the right exposes only imported ledger rectangles. -/
theorem TraceCorQQuotientCandidate.comp_empty_importedRectangles
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      candidate
      TraceCorQQuotientCandidate.empty).importedRectangles =
      [] ++
        (candidate.ledger.importedRectangles ++
          TraceCorQRelationLedger.empty.importedRectangles) :=
  TraceCorQQuotientInput.comp_empty_importedRectangles candidate.input

end AnalyticMotives
end LFunctions
end Boundary
