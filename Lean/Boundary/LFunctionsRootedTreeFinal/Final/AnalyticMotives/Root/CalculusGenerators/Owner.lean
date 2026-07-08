import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CalculusGenerators.Owner

/-!
# Top-root calculus generator wrappers

This file exposes the concrete descent, interval-homotopy, and Tate
representable maps under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes descent channel generator maps. -/
def AnalyticMotivesRoot.descentChannelMap
    (source target : QTraceExpression) :=
  TraceAnalyticMotive.descentChannelMap source target

/-- Descent channel generators are the by-kind channel maps. -/
theorem AnalyticMotivesRoot.descentChannelMap_eq_byKind
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.descentChannelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  TraceAnalyticMotive.descentChannelMap_eq_byKind
    source
    target

/-- The preimage of a descent channel map is the channel trace hom. -/
theorem AnalyticMotivesRoot.descentChannelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.descentChannelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticMotive.descentChannelMap_preimage
    source
    target

/-- The top root exposes descent refinement generator maps. -/
def AnalyticMotivesRoot.descentRefinementMap
    (source target : QTraceExpression) :=
  TraceAnalyticMotive.descentRefinementMap source target

/-- Descent refinement generators are the by-kind refinement maps. -/
theorem AnalyticMotivesRoot.descentRefinementMap_eq_byKind
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.descentRefinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  TraceAnalyticMotive.descentRefinementMap_eq_byKind
    source
    target

/-- The preimage of a descent refinement map is the refinement trace hom. -/
theorem AnalyticMotivesRoot.descentRefinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.descentRefinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticMotive.descentRefinementMap_preimage
    source
    target

/-- The top root exposes descent schedule generator maps. -/
def AnalyticMotivesRoot.descentScheduleMap
    (source target : QTraceExpression) :=
  TraceAnalyticMotive.descentScheduleMap source target

/-- Descent schedule generators are the by-kind schedule maps. -/
theorem AnalyticMotivesRoot.descentScheduleMap_eq_byKind
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.descentScheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  TraceAnalyticMotive.descentScheduleMap_eq_byKind
    source
    target

/-- The preimage of a descent schedule map is the schedule trace hom. -/
theorem AnalyticMotivesRoot.descentScheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.descentScheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticMotive.descentScheduleMap_preimage
    source
    target

/-- The top root exposes interval Stokes generator maps. -/
def AnalyticMotivesRoot.intervalStokesMap
    (source target : QTraceExpression) :=
  TraceAnalyticMotive.intervalStokesMap source target

/-- Interval Stokes generators are the by-kind Stokes maps. -/
theorem AnalyticMotivesRoot.intervalStokesMap_eq_byKind
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.intervalStokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  TraceAnalyticMotive.intervalStokesMap_eq_byKind
    source
    target

/-- The preimage of an interval Stokes map is the Stokes trace hom. -/
theorem AnalyticMotivesRoot.intervalStokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.intervalStokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticMotive.intervalStokesMap_preimage
    source
    target

/-- The top root exposes interval Fubini generator maps. -/
def AnalyticMotivesRoot.intervalFubiniMap
    (source target : QTraceExpression) :=
  TraceAnalyticMotive.intervalFubiniMap source target

/-- Interval Fubini generators are the by-kind Fubini maps. -/
theorem AnalyticMotivesRoot.intervalFubiniMap_eq_byKind
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.intervalFubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  TraceAnalyticMotive.intervalFubiniMap_eq_byKind
    source
    target

/-- The preimage of an interval Fubini map is the Fubini trace hom. -/
theorem AnalyticMotivesRoot.intervalFubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.intervalFubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticMotive.intervalFubiniMap_preimage
    source
    target

/-- The top root exposes Tate weight-drop generator maps. -/
def AnalyticMotivesRoot.tateWeightDropMap
    (source target : QTraceExpression) :=
  TraceAnalyticMotive.tateWeightDropMap source target

/-- Tate weight-drop generators are the by-kind weight-drop maps. -/
theorem AnalyticMotivesRoot.tateWeightDropMap_eq_byKind
    (source target : QTraceExpression) :
    AnalyticMotivesRoot.tateWeightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  TraceAnalyticMotive.tateWeightDropMap_eq_byKind
    source
    target

/-- The preimage of a Tate weight-drop map is the weight-drop trace hom. -/
theorem AnalyticMotivesRoot.tateWeightDropMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (AnalyticMotivesRoot.tateWeightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticMotive.tateWeightDropMap_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
