import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.RewriteMaps.ByKind.Owner

/-!
# Descent generator maps

This file owns the concrete representable-presheaf maps that generate the
descent and refinement calculus before localization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A channel-decomposition map to be imposed by descent. -/
def TraceDescentGenerator.channelMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.channel source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.channel source target).targetObject) :=
  TraceRewriteGenerator.channelRepresentableMap source target

/-- A refinement-invariance map to be imposed by descent. -/
def TraceDescentGenerator.refinementMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.refinement source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.refinement source target).targetObject) :=
  TraceRewriteGenerator.refinementRepresentableMap source target

/-- A schedule-exchange map to be imposed by descent. -/
def TraceDescentGenerator.scheduleMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.schedule source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.schedule source target).targetObject) :=
  TraceRewriteGenerator.scheduleRepresentableMap source target

/-- The descent channel map is the by-kind channel representable map. -/
theorem TraceDescentGenerator.channelMap_eq
    (source target : QTraceExpression) :
    TraceDescentGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  rfl

/-- The descent refinement map is the by-kind refinement representable map. -/
theorem TraceDescentGenerator.refinementMap_eq
    (source target : QTraceExpression) :
    TraceDescentGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  rfl

/-- The descent schedule map is the by-kind schedule representable map. -/
theorem TraceDescentGenerator.scheduleMap_eq
    (source target : QTraceExpression) :
    TraceDescentGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  rfl

/-- The trace preimage of a descent channel map is the channel trace hom. -/
theorem TraceDescentGenerator.channelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceDescentGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.channel source target)

/-- The trace preimage of a descent refinement map is the refinement trace hom. -/
theorem TraceDescentGenerator.refinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceDescentGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.refinement source target)

/-- The trace preimage of a descent schedule map is the schedule trace hom. -/
theorem TraceDescentGenerator.scheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceDescentGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.schedule source target)

end AnalyticMotives
end LFunctions
end Boundary
