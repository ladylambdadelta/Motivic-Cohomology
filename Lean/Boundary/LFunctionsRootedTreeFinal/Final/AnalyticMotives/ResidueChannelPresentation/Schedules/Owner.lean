import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Owner

/-!
# Schedules

This file owns schedules for analytic trace computations.

Schedules record the order in which integrals, summations, contour moves,
residue extractions, and channel decompositions are performed.  Fubini
coherence later proves that admissible schedule changes preserve the trace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A syntactic schedule is a finite list of rewrite kinds. -/
abbrev TraceSchedule :=
  List TraceRewriteKind

/-- The empty trace schedule. -/
def TraceSchedule.empty : TraceSchedule :=
  []

/-- Add one rewrite kind at the front of a trace schedule. -/
def TraceSchedule.cons
    (kind : TraceRewriteKind) (schedule : TraceSchedule) : TraceSchedule :=
  kind :: schedule

/-- The empty trace schedule is the empty list. -/
theorem TraceSchedule.empty_eq_nil :
    TraceSchedule.empty = [] :=
  rfl

/-- Trace-schedule cons is list cons. -/
theorem TraceSchedule.cons_eq_cons
    (kind : TraceRewriteKind)
    (schedule : TraceSchedule) :
    TraceSchedule.cons kind schedule =
      kind :: schedule :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
