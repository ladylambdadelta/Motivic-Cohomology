import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Core.Owner

/-!
# Channel-decomposition rewrite generators

This file owns rewrite generators decomposing boundary trace expressions into
visible analytic channels: arithmetic, archimedean, correction, endpoint,
vertical, horizontal, and tail channels.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A channel rewrite generator has channel kind. -/
theorem TraceRewriteChannelGenerator.kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).kind =
      TraceRewriteKind.channel :=
  TraceRewriteGenerator.channel_kind
    source
    target

/-- A channel rewrite generator has the supplied source. -/
theorem TraceRewriteChannelGenerator.source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).source =
      source :=
  TraceRewriteGenerator.channel_source
    source
    target

/-- A channel rewrite generator has the supplied target. -/
theorem TraceRewriteChannelGenerator.target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).target =
      target :=
  TraceRewriteGenerator.channel_target
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
