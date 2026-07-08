import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Paths.Owner

/-!
# Top-root rewrite paths

This file exposes the concrete finite paths in the analytic trace rewrite
computad under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A top-root identity rewrite path has no one-step generators. -/
theorem AnalyticMotivesRoot.rewritePath_id_stepCount
    (expression : QTraceExpression) :
    (TraceRewritePath.id expression).stepCount =
      0 :=
  TraceRewritePath.id_stepCount
    expression

/-- A top-root identity rewrite path has the supplied source expression. -/
theorem AnalyticMotivesRoot.rewritePath_id_source
    (expression : QTraceExpression) :
    (TraceRewritePath.id expression).source =
      expression :=
  TraceRewritePath.id_source
    expression

/-- A top-root identity rewrite path has the supplied target expression. -/
theorem AnalyticMotivesRoot.rewritePath_id_target
    (expression : QTraceExpression) :
    (TraceRewritePath.id expression).target =
      expression :=
  TraceRewritePath.id_target
    expression

/-- A top-root one-step rewrite path has exactly one generator. -/
theorem AnalyticMotivesRoot.rewritePath_ofGenerator_stepCount
    (generator : TraceRewriteGenerator) :
    (TraceRewritePath.ofGenerator generator).stepCount =
      1 :=
  TraceRewritePath.ofGenerator_stepCount
    generator

/-- A top-root one-step rewrite path has the generator source. -/
theorem AnalyticMotivesRoot.rewritePath_ofGenerator_source
    (generator : TraceRewriteGenerator) :
    (TraceRewritePath.ofGenerator generator).source =
      generator.source :=
  TraceRewritePath.ofGenerator_source
    generator

/-- A top-root one-step rewrite path has the generator target. -/
theorem AnalyticMotivesRoot.rewritePath_ofGenerator_target
    (generator : TraceRewriteGenerator) :
    (TraceRewritePath.ofGenerator generator).target =
      generator.target :=
  TraceRewritePath.ofGenerator_target
    generator

/-- A top-root Stokes path has the supplied source. -/
theorem AnalyticMotivesRoot.stokesRewritePath_source
    (source target : QTraceExpression) :
    (TraceRewritePath.stokes source target).source =
      source :=
  TraceRewritePath.stokes_source
    source
    target

/-- A top-root Stokes path has the supplied target. -/
theorem AnalyticMotivesRoot.stokesRewritePath_target
    (source target : QTraceExpression) :
    (TraceRewritePath.stokes source target).target =
      target :=
  TraceRewritePath.stokes_target
    source
    target

/-- A top-root Stokes path has one rewrite step. -/
theorem AnalyticMotivesRoot.stokesRewritePath_stepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.stokes source target).stepCount =
      1 :=
  TraceRewritePath.stokes_stepCount
    source
    target

/-- A top-root residue path has the supplied source. -/
theorem AnalyticMotivesRoot.residueRewritePath_source
    (source target : QTraceExpression) :
    (TraceRewritePath.residue source target).source =
      source :=
  TraceRewritePath.residue_source
    source
    target

/-- A top-root residue path has the supplied target. -/
theorem AnalyticMotivesRoot.residueRewritePath_target
    (source target : QTraceExpression) :
    (TraceRewritePath.residue source target).target =
      target :=
  TraceRewritePath.residue_target
    source
    target

/-- A top-root residue path has one rewrite step. -/
theorem AnalyticMotivesRoot.residueRewritePath_stepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.residue source target).stepCount =
      1 :=
  TraceRewritePath.residue_stepCount
    source
    target

/-- A top-root channel path has the supplied source. -/
theorem AnalyticMotivesRoot.channelRewritePath_source
    (source target : QTraceExpression) :
    (TraceRewritePath.channel source target).source =
      source :=
  TraceRewritePath.channel_source
    source
    target

/-- A top-root channel path has the supplied target. -/
theorem AnalyticMotivesRoot.channelRewritePath_target
    (source target : QTraceExpression) :
    (TraceRewritePath.channel source target).target =
      target :=
  TraceRewritePath.channel_target
    source
    target

/-- A top-root channel path has one rewrite step. -/
theorem AnalyticMotivesRoot.channelRewritePath_stepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.channel source target).stepCount =
      1 :=
  TraceRewritePath.channel_stepCount
    source
    target

/-- A top-root refinement path has the supplied source. -/
theorem AnalyticMotivesRoot.refinementRewritePath_source
    (source target : QTraceExpression) :
    (TraceRewritePath.refinement source target).source =
      source :=
  TraceRewritePath.refinement_source
    source
    target

/-- A top-root refinement path has the supplied target. -/
theorem AnalyticMotivesRoot.refinementRewritePath_target
    (source target : QTraceExpression) :
    (TraceRewritePath.refinement source target).target =
      target :=
  TraceRewritePath.refinement_target
    source
    target

/-- A top-root refinement path has one rewrite step. -/
theorem AnalyticMotivesRoot.refinementRewritePath_stepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.refinement source target).stepCount =
      1 :=
  TraceRewritePath.refinement_stepCount
    source
    target

/-- A top-root schedule path has the supplied source. -/
theorem AnalyticMotivesRoot.scheduleRewritePath_source
    (source target : QTraceExpression) :
    (TraceRewritePath.schedule source target).source =
      source :=
  TraceRewritePath.schedule_source
    source
    target

/-- A top-root schedule path has the supplied target. -/
theorem AnalyticMotivesRoot.scheduleRewritePath_target
    (source target : QTraceExpression) :
    (TraceRewritePath.schedule source target).target =
      target :=
  TraceRewritePath.schedule_target
    source
    target

/-- A top-root schedule path has one rewrite step. -/
theorem AnalyticMotivesRoot.scheduleRewritePath_stepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.schedule source target).stepCount =
      1 :=
  TraceRewritePath.schedule_stepCount
    source
    target

/-- A top-root weight-drop path has the supplied source. -/
theorem AnalyticMotivesRoot.weightDropRewritePath_source
    (source target : QTraceExpression) :
    (TraceRewritePath.weightDrop source target).source =
      source :=
  TraceRewritePath.weightDrop_source
    source
    target

/-- A top-root weight-drop path has the supplied target. -/
theorem AnalyticMotivesRoot.weightDropRewritePath_target
    (source target : QTraceExpression) :
    (TraceRewritePath.weightDrop source target).target =
      target :=
  TraceRewritePath.weightDrop_target
    source
    target

/-- A top-root weight-drop path has one rewrite step. -/
theorem AnalyticMotivesRoot.weightDropRewritePath_stepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.weightDrop source target).stepCount =
      1 :=
  TraceRewritePath.weightDrop_stepCount
    source
    target

/-- A top-root Fubini path has the supplied source. -/
theorem AnalyticMotivesRoot.fubiniRewritePath_source
    (source target : QTraceExpression) :
    (TraceRewritePath.fubini source target).source =
      source :=
  TraceRewritePath.fubini_source
    source
    target

/-- A top-root Fubini path has the supplied target. -/
theorem AnalyticMotivesRoot.fubiniRewritePath_target
    (source target : QTraceExpression) :
    (TraceRewritePath.fubini source target).target =
      target :=
  TraceRewritePath.fubini_target
    source
    target

/-- A top-root Fubini path has one rewrite step. -/
theorem AnalyticMotivesRoot.fubiniRewritePath_stepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.fubini source target).stepCount =
      1 :=
  TraceRewritePath.fubini_stepCount
    source
    target

/-- A top-root concatenated path has the source of its first path. -/
theorem AnalyticMotivesRoot.rewritePath_comp_source
    (first second : TraceRewritePath) :
    (TraceRewritePath.comp first second).source =
      first.source :=
  TraceRewritePath.comp_source
    first
    second

/-- A top-root concatenated path has the target of its second path. -/
theorem AnalyticMotivesRoot.rewritePath_comp_target
    (first second : TraceRewritePath) :
    (TraceRewritePath.comp first second).target =
      second.target :=
  TraceRewritePath.comp_target
    first
    second

/-- A top-root concatenated path adds the step counts of its factors. -/
theorem AnalyticMotivesRoot.rewritePath_comp_stepCount
    (first second : TraceRewritePath) :
    (TraceRewritePath.comp first second).stepCount =
      first.stepCount + second.stepCount :=
  TraceRewritePath.comp_stepCount
    first
    second

end AnalyticMotives
end LFunctions
end Boundary
