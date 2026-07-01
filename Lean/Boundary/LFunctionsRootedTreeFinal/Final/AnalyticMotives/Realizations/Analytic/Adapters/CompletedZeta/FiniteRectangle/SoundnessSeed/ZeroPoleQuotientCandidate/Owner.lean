import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleQuotientInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Owner

/-!
# Zero-pole quotient candidate

This file packages the completed-zeta zero-pole quotient input as a raw
candidate representative.

No equivalence relation is imposed here.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The raw quotient candidate for the completed-zeta zero-pole seed. -/
def completedZetaZeroPoleTraceCorQQuotientCandidate :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientCandidate.ofInput
    completedZetaZeroPoleTraceCorQQuotientInput

/-- The zero-pole quotient candidate has the zero-pole quotient input. -/
theorem completedZetaZeroPoleTraceCorQQuotientCandidate_input :
    completedZetaZeroPoleTraceCorQQuotientCandidate.input =
      completedZetaZeroPoleTraceCorQQuotientInput :=
  rfl

/-- The zero-pole quotient candidate has the zero-pole formal sum. -/
theorem completedZetaZeroPoleTraceCorQQuotientCandidate_formalSum :
    completedZetaZeroPoleTraceCorQQuotientCandidate.formalSum =
      completedZetaZeroPoleAnalyticChainTraceCorQFormalSum :=
  rfl

/-- The zero-pole quotient candidate has the zero-pole relation ledger. -/
theorem completedZetaZeroPoleTraceCorQQuotientCandidate_ledger :
    completedZetaZeroPoleTraceCorQQuotientCandidate.ledger =
      completedZetaZeroPoleTraceCorQRelationLedger :=
  rfl

/-- Adding the empty candidate on the left preserves the zero-pole candidate. -/
theorem completedZetaZeroPoleTraceCorQQuotientCandidate_empty_add :
    TraceCorQQuotientCandidate.add
      TraceCorQQuotientCandidate.empty
      completedZetaZeroPoleTraceCorQQuotientCandidate =
      completedZetaZeroPoleTraceCorQQuotientCandidate :=
  rfl

/-- Adding the empty candidate on the right preserves the zero-pole candidate. -/
theorem completedZetaZeroPoleTraceCorQQuotientCandidate_add_empty :
    TraceCorQQuotientCandidate.add
      completedZetaZeroPoleTraceCorQQuotientCandidate
      TraceCorQQuotientCandidate.empty =
      completedZetaZeroPoleTraceCorQQuotientCandidate :=
  TraceCorQQuotientCandidate.add_empty
    completedZetaZeroPoleTraceCorQQuotientCandidate

end AnalyticMotives
end LFunctions
end Boundary
