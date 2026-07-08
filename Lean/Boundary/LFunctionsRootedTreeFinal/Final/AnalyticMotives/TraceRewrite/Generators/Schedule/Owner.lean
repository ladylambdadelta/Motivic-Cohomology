import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Core.Owner

/-!
# Schedule rewrite generators

This file owns rewrites associated to cofinal schedules through admissible
refinement parameters.  Schedules realize directed paths avoiding bad loci while
preserving residue windows and controlling tails.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A schedule rewrite generator has schedule kind. -/
theorem TraceRewriteScheduleGenerator.kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.schedule source target).kind =
      TraceRewriteKind.schedule :=
  TraceRewriteGenerator.schedule_kind
    source
    target

/-- A schedule rewrite generator has the supplied source. -/
theorem TraceRewriteScheduleGenerator.source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.schedule source target).source =
      source :=
  TraceRewriteGenerator.schedule_source
    source
    target

/-- A schedule rewrite generator has the supplied target. -/
theorem TraceRewriteScheduleGenerator.target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.schedule source target).target =
      target :=
  TraceRewriteGenerator.schedule_target
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
