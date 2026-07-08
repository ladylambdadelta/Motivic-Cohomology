import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.RewriteMaps.ByKind.Maps.Owner

/-!
# Analytic realization generator maps

This file owns concrete representable-presheaf maps used by the analytic
realization layer before any comparison or localization theorem is stated.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Stokes map used by the analytic trace-value realization. -/
def TraceAnalyticRealizationGenerator.stokesMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.stokes source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.stokes source target).targetObject) :=
  TraceRewriteGenerator.stokesRepresentableMap source target

/-- A residue-extraction map used by the analytic trace-value realization. -/
def TraceAnalyticRealizationGenerator.residueMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.residue source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.residue source target).targetObject) :=
  TraceRewriteGenerator.residueRepresentableMap source target

/-- A channel-decomposition map used by the analytic trace-value realization. -/
def TraceAnalyticRealizationGenerator.channelMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.channel source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.channel source target).targetObject) :=
  TraceRewriteGenerator.channelRepresentableMap source target

/-- A refinement-invariance map used by the analytic trace-value realization. -/
def TraceAnalyticRealizationGenerator.refinementMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.refinement source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.refinement source target).targetObject) :=
  TraceRewriteGenerator.refinementRepresentableMap source target

/-- A schedule-exchange map used by the analytic trace-value realization. -/
def TraceAnalyticRealizationGenerator.scheduleMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.schedule source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.schedule source target).targetObject) :=
  TraceRewriteGenerator.scheduleRepresentableMap source target

/-- A weight-drop map used by the analytic trace-value realization. -/
def TraceAnalyticRealizationGenerator.weightDropMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.weightDrop source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.weightDrop source target).targetObject) :=
  TraceRewriteGenerator.weightDropRepresentableMap source target

/-- A Fubini-interchange map used by the analytic trace-value realization. -/
def TraceAnalyticRealizationGenerator.fubiniMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.fubini source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.fubini source target).targetObject) :=
  TraceRewriteGenerator.fubiniRepresentableMap source target

/-- The analytic realization Stokes map is the by-kind Stokes representable map. -/
theorem TraceAnalyticRealizationGenerator.stokesMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  rfl

/-- The analytic realization residue map is the by-kind residue representable map. -/
theorem TraceAnalyticRealizationGenerator.residueMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  rfl

/-- The analytic realization channel map is the by-kind channel representable map. -/
theorem TraceAnalyticRealizationGenerator.channelMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  rfl

/-- The analytic realization refinement map is the by-kind refinement representable map. -/
theorem TraceAnalyticRealizationGenerator.refinementMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  rfl

/-- The analytic realization schedule map is the by-kind schedule representable map. -/
theorem TraceAnalyticRealizationGenerator.scheduleMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  rfl

/-- The analytic realization weight-drop map is the by-kind weight-drop representable map. -/
theorem TraceAnalyticRealizationGenerator.weightDropMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  rfl

/-- The analytic realization Fubini map is the by-kind Fubini representable map. -/
theorem TraceAnalyticRealizationGenerator.fubiniMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  rfl

/-- The trace preimage of an analytic realization Stokes map is the Stokes trace hom. -/
theorem TraceAnalyticRealizationGenerator.stokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.stokes source target)

/-- The trace preimage of an analytic realization residue map is the residue trace hom. -/
theorem TraceAnalyticRealizationGenerator.residueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.residue source target)

/-- The trace preimage of an analytic realization channel map is the channel trace hom. -/
theorem TraceAnalyticRealizationGenerator.channelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.channel source target)

/-- The trace preimage of an analytic realization refinement map is the refinement trace hom. -/
theorem TraceAnalyticRealizationGenerator.refinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.refinement source target)

/-- The trace preimage of an analytic realization schedule map is the schedule trace hom. -/
theorem TraceAnalyticRealizationGenerator.scheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.schedule source target)

/-- The trace preimage of an analytic realization weight-drop map is the weight-drop trace hom. -/
theorem TraceAnalyticRealizationGenerator.weightDropMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.weightDrop source target)

/-- The trace preimage of an analytic realization Fubini map is the Fubini trace hom. -/
theorem TraceAnalyticRealizationGenerator.fubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.fubini source target)

end AnalyticMotives
end LFunctions
end Boundary
