import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Core.Owner

/-!
# Residue rewrite generators

This file owns rewrite generators turning boundary trace expressions into
residue-ledger expressions.  These are the formal counterparts of residue
theorems and local residue extraction.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A residue rewrite generator has residue kind. -/
theorem TraceRewriteResidueGenerator.kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).kind =
      TraceRewriteKind.residue :=
  TraceRewriteGenerator.residue_kind
    source
    target

/-- A residue rewrite generator has the supplied source. -/
theorem TraceRewriteResidueGenerator.source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).source =
      source :=
  TraceRewriteGenerator.residue_source
    source
    target

/-- A residue rewrite generator has the supplied target. -/
theorem TraceRewriteResidueGenerator.target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).target =
      target :=
  TraceRewriteGenerator.residue_target
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
