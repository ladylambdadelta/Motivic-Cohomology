import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleAnalyticChain.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRelationLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Owner

/-!
# Zero-pole quotient input

This file packages the completed-zeta zero-pole formal trace-correspondence sum
with its finite relation ledger as a pre-quotient input.

No quotient is imposed here.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The pre-quotient input for the completed-zeta zero-pole seed. -/
def completedZetaZeroPoleTraceCorQQuotientInput :
    TraceCorQQuotientInput :=
  TraceCorQQuotientInput.ofFormalSumLedger
    completedZetaZeroPoleAnalyticChainTraceCorQFormalSum
    completedZetaZeroPoleTraceCorQRelationLedger

/-- The zero-pole quotient input has the analytic chain formal sum. -/
theorem completedZetaZeroPoleTraceCorQQuotientInput_formalSum :
    completedZetaZeroPoleTraceCorQQuotientInput.formalSum =
      completedZetaZeroPoleAnalyticChainTraceCorQFormalSum :=
  rfl

/-- The zero-pole quotient input has the zero-pole relation ledger. -/
theorem completedZetaZeroPoleTraceCorQQuotientInput_ledger :
    completedZetaZeroPoleTraceCorQQuotientInput.ledger =
      completedZetaZeroPoleTraceCorQRelationLedger :=
  rfl

/-- Adding the empty quotient input on the left preserves the zero-pole quotient input. -/
theorem completedZetaZeroPoleTraceCorQQuotientInput_empty_add :
    TraceCorQQuotientInput.add
      TraceCorQQuotientInput.empty
      completedZetaZeroPoleTraceCorQQuotientInput =
      completedZetaZeroPoleTraceCorQQuotientInput :=
  rfl

/-- Adding the empty quotient input on the right preserves the zero-pole quotient input. -/
theorem completedZetaZeroPoleTraceCorQQuotientInput_add_empty :
    TraceCorQQuotientInput.add
      completedZetaZeroPoleTraceCorQQuotientInput
      TraceCorQQuotientInput.empty =
      completedZetaZeroPoleTraceCorQQuotientInput :=
  TraceCorQQuotientInput.add_empty
    completedZetaZeroPoleTraceCorQQuotientInput

end AnalyticMotives
end LFunctions
end Boundary
