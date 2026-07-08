import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Descent.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.IntervalHomotopy.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.TateStabilization.Generators.Owner

/-!
# Motive-root calculus generator wrappers

This file exposes the concrete descent, interval-homotopy, and Tate
representable maps at the motive root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The motive root exposes descent channel generator maps. -/
def TraceAnalyticMotive.descentChannelMap
    (source target : QTraceExpression) :=
  TraceDescentGenerator.channelMap source target

/-- Descent channel generators are the by-kind channel maps. -/
theorem TraceAnalyticMotive.descentChannelMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticMotive.descentChannelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  TraceDescentGenerator.channelMap_eq
    source
    target

/-- The preimage of a descent channel map is the channel trace hom. -/
theorem TraceAnalyticMotive.descentChannelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.descentChannelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceDescentGenerator.channelMap_preimage
    source
    target

/-- The motive root exposes descent refinement generator maps. -/
def TraceAnalyticMotive.descentRefinementMap
    (source target : QTraceExpression) :=
  TraceDescentGenerator.refinementMap source target

/-- Descent refinement generators are the by-kind refinement maps. -/
theorem TraceAnalyticMotive.descentRefinementMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticMotive.descentRefinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  TraceDescentGenerator.refinementMap_eq
    source
    target

/-- The preimage of a descent refinement map is the refinement trace hom. -/
theorem TraceAnalyticMotive.descentRefinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.descentRefinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceDescentGenerator.refinementMap_preimage
    source
    target

/-- The motive root exposes descent schedule generator maps. -/
def TraceAnalyticMotive.descentScheduleMap
    (source target : QTraceExpression) :=
  TraceDescentGenerator.scheduleMap source target

/-- Descent schedule generators are the by-kind schedule maps. -/
theorem TraceAnalyticMotive.descentScheduleMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticMotive.descentScheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  TraceDescentGenerator.scheduleMap_eq
    source
    target

/-- The preimage of a descent schedule map is the schedule trace hom. -/
theorem TraceAnalyticMotive.descentScheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.descentScheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceDescentGenerator.scheduleMap_preimage
    source
    target

/-- The motive root exposes interval Stokes generator maps. -/
def TraceAnalyticMotive.intervalStokesMap
    (source target : QTraceExpression) :=
  TraceIntervalHomotopyGenerator.stokesMap source target

/-- Interval Stokes generators are the by-kind Stokes maps. -/
theorem TraceAnalyticMotive.intervalStokesMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticMotive.intervalStokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  TraceIntervalHomotopyGenerator.stokesMap_eq
    source
    target

/-- The preimage of an interval Stokes map is the Stokes trace hom. -/
theorem TraceAnalyticMotive.intervalStokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.intervalStokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceIntervalHomotopyGenerator.stokesMap_preimage
    source
    target

/-- The motive root exposes interval Fubini generator maps. -/
def TraceAnalyticMotive.intervalFubiniMap
    (source target : QTraceExpression) :=
  TraceIntervalHomotopyGenerator.fubiniMap source target

/-- Interval Fubini generators are the by-kind Fubini maps. -/
theorem TraceAnalyticMotive.intervalFubiniMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticMotive.intervalFubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  TraceIntervalHomotopyGenerator.fubiniMap_eq
    source
    target

/-- The preimage of an interval Fubini map is the Fubini trace hom. -/
theorem TraceAnalyticMotive.intervalFubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.intervalFubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceIntervalHomotopyGenerator.fubiniMap_preimage
    source
    target

/-- The motive root exposes Tate weight-drop generator maps. -/
def TraceAnalyticMotive.tateWeightDropMap
    (source target : QTraceExpression) :=
  TraceTateStabilizationGenerator.weightDropMap source target

/-- Tate weight-drop generators are the by-kind weight-drop maps. -/
theorem TraceAnalyticMotive.tateWeightDropMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticMotive.tateWeightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  TraceTateStabilizationGenerator.weightDropMap_eq
    source
    target

/-- The preimage of a Tate weight-drop map is the weight-drop trace hom. -/
theorem TraceAnalyticMotive.tateWeightDropMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticMotive.tateWeightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceTateStabilizationGenerator.weightDropMap_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
