import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.RewriteMaps.ByKind.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.RewriteMaps.ByKind.Facts.Owner

/-!
# Top-root by-kind trace-hom equality facts
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top-root Stokes trace morphism is the generic trace morphism. -/
theorem AnalyticMotivesRoot.stokesTraceHom_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.stokesTraceHom source target =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticMotive.stokesTraceHom_eq
    source
    target

/-- The top-root residue trace morphism is the generic trace morphism. -/
theorem AnalyticMotivesRoot.residueTraceHom_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.residueTraceHom source target =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticMotive.residueTraceHom_eq
    source
    target

/-- The top-root channel trace morphism is the generic trace morphism. -/
theorem AnalyticMotivesRoot.channelTraceHom_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.channelTraceHom source target =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticMotive.channelTraceHom_eq
    source
    target

/-- The top-root refinement trace morphism is the generic trace morphism. -/
theorem AnalyticMotivesRoot.refinementTraceHom_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.refinementTraceHom source target =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticMotive.refinementTraceHom_eq
    source
    target

/-- The top-root schedule trace morphism is the generic trace morphism. -/
theorem AnalyticMotivesRoot.scheduleTraceHom_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.scheduleTraceHom source target =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticMotive.scheduleTraceHom_eq
    source
    target

/-- The top-root weight-drop trace morphism is the generic trace morphism. -/
theorem AnalyticMotivesRoot.weightDropTraceHom_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.weightDropTraceHom source target =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticMotive.weightDropTraceHom_eq
    source
    target

/-- The top-root Fubini trace morphism is the generic trace morphism. -/
theorem AnalyticMotivesRoot.fubiniTraceHom_eq
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.fubiniTraceHom source target =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticMotive.fubiniTraceHom_eq
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
