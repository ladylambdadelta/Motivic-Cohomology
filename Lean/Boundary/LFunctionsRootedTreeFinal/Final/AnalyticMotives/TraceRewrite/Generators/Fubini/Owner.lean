import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Core.Owner

/-!
# Fubini coherence generators

This file owns the analytic rewrite generators and coherence targets expressing
that independent integrations, summations, residues, and channel decompositions
can be interchanged under the appropriate hypotheses.

Fubini is the analytic source of associativity for composed trace transports.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini rewrite generator has Fubini kind. -/
theorem TraceRewriteFubiniGenerator.kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.fubini source target).kind =
      TraceRewriteKind.fubini :=
  TraceRewriteGenerator.fubini_kind
    source
    target

/-- A Fubini rewrite generator has the supplied source. -/
theorem TraceRewriteFubiniGenerator.source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.fubini source target).source =
      source :=
  TraceRewriteGenerator.fubini_source
    source
    target

/-- A Fubini rewrite generator has the supplied target. -/
theorem TraceRewriteFubiniGenerator.target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.fubini source target).target =
      target :=
  TraceRewriteGenerator.fubini_target
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
