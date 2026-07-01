import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Relations.Owner

/-!
# Zero-pole trace-correspondence relation generator

This file records the first Q-linear relation generator supported by the
completed-zeta finite-rectangle adapter.

The relation generator is only a coherence cell together with the formal
Q-linear support it governs.  It does not quotient morphisms, and it does not
assert that residue and channel generators are equal as correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero-pole residue-channel relation generator in the trace-correspondence calculus. -/
def completedZetaZeroPoleResidueChannelTraceCorQRelationGenerator :
    TraceCorQRelationGenerator :=
  TraceCorQRelationGenerator.ofCellSupport
    completedZetaZeroPoleResidueChannelCoherenceCell
    completedZetaZeroPoleAnalyticChainTraceCorQFormalSum

/-- The zero-pole trace-correspondence relation is supported by the residue-channel cell. -/
theorem completedZetaZeroPoleResidueChannelTraceCorQRelationGenerator_cell :
    completedZetaZeroPoleResidueChannelTraceCorQRelationGenerator.cell =
      completedZetaZeroPoleResidueChannelCoherenceCell :=
  rfl

/-- The zero-pole trace-correspondence relation has the analytic chain formal support. -/
theorem completedZetaZeroPoleResidueChannelTraceCorQRelationGenerator_support :
    completedZetaZeroPoleResidueChannelTraceCorQRelationGenerator.support =
      completedZetaZeroPoleAnalyticChainTraceCorQFormalSum :=
  rfl

/-- The support of the zero-pole relation is residue plus channel. -/
theorem completedZetaZeroPoleResidueChannelTraceCorQRelationGenerator_support_eq :
    completedZetaZeroPoleResidueChannelTraceCorQRelationGenerator.support =
      TraceCorQFormalSum.add
        completedZetaZeroPoleResidueTraceCorQFormalSum
        completedZetaZeroPoleChannelTraceCorQFormalSum :=
  completedZetaZeroPoleAnalyticChainTraceCorQFormalSum_eq

end AnalyticMotives
end LFunctions
end Boundary
