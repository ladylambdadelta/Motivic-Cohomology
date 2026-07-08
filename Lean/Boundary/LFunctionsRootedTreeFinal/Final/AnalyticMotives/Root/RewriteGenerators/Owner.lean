import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Generators.Core.Owner

/-!
# Top-root rewrite generators

This file exposes the concrete one-step analytic trace rewrite generators under
the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A top-root Stokes rewrite generator has Stokes kind. -/
theorem AnalyticMotivesRoot.stokesRewriteGenerator_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).kind =
      TraceRewriteKind.stokes :=
  TraceRewriteGenerator.stokes_kind
    source
    target

/-- A top-root Stokes rewrite generator has the supplied source. -/
theorem AnalyticMotivesRoot.stokesRewriteGenerator_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).source =
      source :=
  TraceRewriteGenerator.stokes_source
    source
    target

/-- A top-root Stokes rewrite generator has the supplied target. -/
theorem AnalyticMotivesRoot.stokesRewriteGenerator_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.stokes source target).target =
      target :=
  TraceRewriteGenerator.stokes_target
    source
    target

/-- A top-root residue rewrite generator has residue kind. -/
theorem AnalyticMotivesRoot.residueRewriteGenerator_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).kind =
      TraceRewriteKind.residue :=
  TraceRewriteGenerator.residue_kind
    source
    target

/-- A top-root residue rewrite generator has the supplied source. -/
theorem AnalyticMotivesRoot.residueRewriteGenerator_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).source =
      source :=
  TraceRewriteGenerator.residue_source
    source
    target

/-- A top-root residue rewrite generator has the supplied target. -/
theorem AnalyticMotivesRoot.residueRewriteGenerator_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.residue source target).target =
      target :=
  TraceRewriteGenerator.residue_target
    source
    target

/-- A top-root channel rewrite generator has channel kind. -/
theorem AnalyticMotivesRoot.channelRewriteGenerator_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).kind =
      TraceRewriteKind.channel :=
  TraceRewriteGenerator.channel_kind
    source
    target

/-- A top-root channel rewrite generator has the supplied source. -/
theorem AnalyticMotivesRoot.channelRewriteGenerator_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).source =
      source :=
  TraceRewriteGenerator.channel_source
    source
    target

/-- A top-root channel rewrite generator has the supplied target. -/
theorem AnalyticMotivesRoot.channelRewriteGenerator_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.channel source target).target =
      target :=
  TraceRewriteGenerator.channel_target
    source
    target

/-- A top-root refinement rewrite generator has refinement kind. -/
theorem AnalyticMotivesRoot.refinementRewriteGenerator_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.refinement source target).kind =
      TraceRewriteKind.refinement :=
  TraceRewriteGenerator.refinement_kind
    source
    target

/-- A top-root refinement rewrite generator has the supplied source. -/
theorem AnalyticMotivesRoot.refinementRewriteGenerator_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.refinement source target).source =
      source :=
  TraceRewriteGenerator.refinement_source
    source
    target

/-- A top-root refinement rewrite generator has the supplied target. -/
theorem AnalyticMotivesRoot.refinementRewriteGenerator_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.refinement source target).target =
      target :=
  TraceRewriteGenerator.refinement_target
    source
    target

/-- A top-root schedule rewrite generator has schedule kind. -/
theorem AnalyticMotivesRoot.scheduleRewriteGenerator_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.schedule source target).kind =
      TraceRewriteKind.schedule :=
  TraceRewriteGenerator.schedule_kind
    source
    target

/-- A top-root schedule rewrite generator has the supplied source. -/
theorem AnalyticMotivesRoot.scheduleRewriteGenerator_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.schedule source target).source =
      source :=
  TraceRewriteGenerator.schedule_source
    source
    target

/-- A top-root schedule rewrite generator has the supplied target. -/
theorem AnalyticMotivesRoot.scheduleRewriteGenerator_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.schedule source target).target =
      target :=
  TraceRewriteGenerator.schedule_target
    source
    target

/-- A top-root weight-drop rewrite generator has weight-drop kind. -/
theorem AnalyticMotivesRoot.weightDropRewriteGenerator_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.weightDrop source target).kind =
      TraceRewriteKind.weightDrop :=
  TraceRewriteGenerator.weightDrop_kind
    source
    target

/-- A top-root weight-drop rewrite generator has the supplied source. -/
theorem AnalyticMotivesRoot.weightDropRewriteGenerator_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.weightDrop source target).source =
      source :=
  TraceRewriteGenerator.weightDrop_source
    source
    target

/-- A top-root weight-drop rewrite generator has the supplied target. -/
theorem AnalyticMotivesRoot.weightDropRewriteGenerator_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.weightDrop source target).target =
      target :=
  TraceRewriteGenerator.weightDrop_target
    source
    target

/-- A top-root Fubini rewrite generator has Fubini kind. -/
theorem AnalyticMotivesRoot.fubiniRewriteGenerator_kind
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.fubini source target).kind =
      TraceRewriteKind.fubini :=
  TraceRewriteGenerator.fubini_kind
    source
    target

/-- A top-root Fubini rewrite generator has the supplied source. -/
theorem AnalyticMotivesRoot.fubiniRewriteGenerator_source
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.fubini source target).source =
      source :=
  TraceRewriteGenerator.fubini_source
    source
    target

/-- A top-root Fubini rewrite generator has the supplied target. -/
theorem AnalyticMotivesRoot.fubiniRewriteGenerator_target
    (source target : QTraceExpression) :
    (TraceRewriteGenerator.fubini source target).target =
      target :=
  TraceRewriteGenerator.fubini_target
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
