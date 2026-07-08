import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.QuotientInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Core.Owner

/-!
# Quotient-candidate carriers for analytic effective realization

This file exposes the raw candidate used by the trace-correspondence quotient.
Candidates are the pre-quotient objects that representatives map to before
the quotient relation is imposed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual trace-correspondence quotient candidate. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientCandidateCarrier
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate :=
  candidate

/-- The quotient input represented by a quotient candidate. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientCandidateInput
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotientInput :=
  candidate.input

/-- The raw formal sum represented by a quotient candidate. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientCandidateFormalSum
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQFormalSum :=
  candidate.formalSum

/-- The relation ledger represented by a quotient candidate. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientCandidateLedger
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationLedger :=
  candidate.ledger

/-- The certificate ledger represented by a quotient candidate. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientCandidateCertificateLedger
    (candidate : TraceCorQQuotientCandidate) :
    ResidueChannelCertificateLedger :=
  candidate.certificateLedger

/-- The imported finite-rectangle count represented by a quotient candidate. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientCandidateImportedRectangleCount
    (candidate : TraceCorQQuotientCandidate) :
    Nat :=
  candidate.importedRectangleCount

/-- The imported finite rectangles represented by a quotient candidate. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientCandidateImportedRectangles
    (candidate : TraceCorQQuotientCandidate) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  candidate.importedRectangles

/-- The trace-bookkeeping count represented by a quotient candidate. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientCandidateTraceBookkeepingCount
    (candidate : TraceCorQQuotientCandidate) :
    Nat :=
  candidate.traceBookkeepingCount

/-- The rewrite-step count represented by a quotient candidate. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientCandidateRewriteStepCount
    (candidate : TraceCorQQuotientCandidate) :
    Nat :=
  candidate.rewriteStepCount

/-- The quotient-candidate carrier is definitionally the supplied candidate. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientCandidateCarrier_eq
    (candidate : TraceCorQQuotientCandidate) :
    TraceAnalyticEffectiveRealization.traceHomQuotientCandidateCarrier candidate =
      candidate :=
  rfl

/-- The quotient-candidate input carrier is definitionally its input. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientCandidateInput_eq
    (candidate : TraceCorQQuotientCandidate) :
    TraceAnalyticEffectiveRealization.traceHomQuotientCandidateInput candidate =
      candidate.input :=
  rfl

/-- The quotient-candidate formal-sum carrier is definitionally its formal sum. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientCandidateFormalSum_eq
    (candidate : TraceCorQQuotientCandidate) :
    TraceAnalyticEffectiveRealization.traceHomQuotientCandidateFormalSum candidate =
      candidate.formalSum :=
  rfl

/-- The quotient-candidate relation-ledger carrier is definitionally its ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientCandidateLedger_eq
    (candidate : TraceCorQQuotientCandidate) :
    TraceAnalyticEffectiveRealization.traceHomQuotientCandidateLedger candidate =
      candidate.ledger :=
  rfl

/-- A quotient candidate's certificate ledger appends formal-sum and ledger certificates. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientCandidateCertificateLedger_eq_append
    (candidate : TraceCorQQuotientCandidate) :
    TraceAnalyticEffectiveRealization.traceHomQuotientCandidateCertificateLedger candidate =
      ResidueChannelCertificateLedger.append
        candidate.formalSum.certificateLedger
        candidate.ledger.certificateLedger :=
  rfl

/-- A quotient candidate's imported count is the length of its imported rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientCandidateImportedRectangleCount_eq_length
    (candidate : TraceCorQQuotientCandidate) :
    TraceAnalyticEffectiveRealization.traceHomQuotientCandidateImportedRectangleCount candidate =
      (TraceAnalyticEffectiveRealization.traceHomQuotientCandidateImportedRectangles
        candidate).length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    candidate.certificateLedger

end AnalyticMotives
end LFunctions
end Boundary
