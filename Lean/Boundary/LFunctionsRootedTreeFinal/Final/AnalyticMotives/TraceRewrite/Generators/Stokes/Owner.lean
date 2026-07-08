import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Core.Owner

/-!
# Stokes rewrite generators

This file owns rewrite generators expressing Stokes cancellation for analytic
trace expressions.  A Stokes rewrite is a directed analytic identity between
formal boundary expressions, later realized by complex-analytic theorems.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Stokes rewrite generator has Stokes kind. -/
theorem TraceRewriteStokesGenerator.kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).kind =
      TraceRewriteKind.stokes :=
  TraceRewriteGenerator.stokes_kind
    source
    target

/-- A Stokes rewrite generator has the supplied source. -/
theorem TraceRewriteStokesGenerator.source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).source =
      source :=
  TraceRewriteGenerator.stokes_source
    source
    target

/-- A Stokes rewrite generator has the supplied target. -/
theorem TraceRewriteStokesGenerator.target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).target =
      target :=
  TraceRewriteGenerator.stokes_target
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
