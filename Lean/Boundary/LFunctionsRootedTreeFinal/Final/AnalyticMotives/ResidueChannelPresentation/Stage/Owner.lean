import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.Atoms.Owner

/-!
# Residue-channel stages

This file owns the concrete stage labels for residue-channel trace
presentations.

A stage is a position in an analytic trace computation: the expression before a
contour move, after a residue extraction, after a channel split, after a
refinement, or after a scheduling exchange.  Stages are part of the trace
presentation itself; they are not motive objects and they are not rectangles.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A presentation stage is a syntactic stage index in the trace calculus. -/
abbrev ResidueChannelStage :=
  TraceStageIndex

end AnalyticMotives
end LFunctions
end Boundary
