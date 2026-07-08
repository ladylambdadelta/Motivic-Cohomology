import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Schedules.Owner

/-!
# Top-root trace schedules

This file exposes finite schedules for analytic trace computations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the empty trace schedule. -/
def AnalyticMotivesRoot.traceSchedule_empty : TraceSchedule :=
  TraceSchedule.empty

/-- The top root exposes trace-schedule cons. -/
def AnalyticMotivesRoot.traceSchedule_cons
    (kind : TraceRewriteKind) (schedule : TraceSchedule) :
    TraceSchedule :=
  TraceSchedule.cons kind schedule

/-- The top root exposes the empty trace schedule as the empty list. -/
theorem AnalyticMotivesRoot.traceSchedule_empty_eq_nil :
    TraceSchedule.empty = [] :=
  TraceSchedule.empty_eq_nil

/-- The top root exposes trace-schedule cons as list cons. -/
theorem AnalyticMotivesRoot.traceSchedule_cons_eq_cons
    (kind : TraceRewriteKind)
    (schedule : TraceSchedule) :
    TraceSchedule.cons kind schedule =
      kind :: schedule :=
  TraceSchedule.cons_eq_cons kind schedule

end AnalyticMotives
end LFunctions
end Boundary
