import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Stage.Owner

/-!
# Top-root residue-channel stages

This file exposes the residue-channel stage type used by finite analytic trace
presentations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes residue-channel stages as trace-stage indices. -/
def AnalyticMotivesRoot.residueChannelStage
    (stage : ResidueChannelStage) :
    TraceStageIndex :=
  stage

end AnalyticMotives
end LFunctions
end Boundary
