import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Core.Owner

/-!
# Refinement rewrite generators

This file owns directed rewrites comparing trace expressions at different
admissible refinement stages: height changes, contour deformations, deletion
radii, truncation windows, and scheduled finite approximants.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A refinement rewrite generator has refinement kind. -/
theorem TraceRewriteRefinementGenerator.kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.refinement source target).kind =
      TraceRewriteKind.refinement :=
  TraceRewriteGenerator.refinement_kind
    source
    target

/-- A refinement rewrite generator has the supplied source. -/
theorem TraceRewriteRefinementGenerator.source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.refinement source target).source =
      source :=
  TraceRewriteGenerator.refinement_source
    source
    target

/-- A refinement rewrite generator has the supplied target. -/
theorem TraceRewriteRefinementGenerator.target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.refinement source target).target =
      target :=
  TraceRewriteGenerator.refinement_target
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
