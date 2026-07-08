import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Core.Owner

/-!
# Weight-drop rewrite generators

This file owns rewrites sending controlled defects and tails either to zero or
to explicitly lower-weight trace expressions.  These rewrites are the analytic
source of the later motivic weight filtration.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A weight-drop rewrite generator has weight-drop kind. -/
theorem TraceRewriteWeightDropGenerator.kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.weightDrop source target).kind =
      TraceRewriteKind.weightDrop :=
  TraceRewriteGenerator.weightDrop_kind
    source
    target

/-- A weight-drop rewrite generator has the supplied source. -/
theorem TraceRewriteWeightDropGenerator.source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.weightDrop source target).source =
      source :=
  TraceRewriteGenerator.weightDrop_source
    source
    target

/-- A weight-drop rewrite generator has the supplied target. -/
theorem TraceRewriteWeightDropGenerator.target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.weightDrop source target).target =
      target :=
  TraceRewriteGenerator.weightDrop_target
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
