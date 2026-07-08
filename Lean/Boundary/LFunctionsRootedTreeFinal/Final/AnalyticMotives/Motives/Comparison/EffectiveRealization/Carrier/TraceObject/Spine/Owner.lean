import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Objects.Owner

/-!
# Trace-object spine inputs for effective realization

This file exposes the certified presentation spine carried by a trace object
and the component projections from that spine.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The certified presentation spine carried by a trace-object carrier input. -/
def TraceAnalyticEffectiveRealization.traceObjectSpine
    (object : TraceCorQObject) :
    ResidueChannelPresentationSpine :=
  object.spine

/-- The trace-object source is the source of its certified spine. -/
theorem TraceAnalyticEffectiveRealization.traceObject_source_eq_spine_source
    (object : TraceCorQObject) :
    object.source =
      (TraceAnalyticEffectiveRealization.traceObjectSpine object).source :=
  rfl

/-- The trace-object residue ledger is the ledger of its certified spine. -/
theorem TraceAnalyticEffectiveRealization.traceObject_ledger_eq_spine_ledger
    (object : TraceCorQObject) :
    object.ledger =
      (TraceAnalyticEffectiveRealization.traceObjectSpine object).ledger :=
  rfl

/-- The trace-object channel list is the channel list of its certified spine. -/
theorem TraceAnalyticEffectiveRealization.traceObject_channels_eq_spine_channels
    (object : TraceCorQObject) :
    object.channels =
      (TraceAnalyticEffectiveRealization.traceObjectSpine object).channels :=
  rfl

/-- The trace-object schedule is the schedule of its certified spine. -/
theorem TraceAnalyticEffectiveRealization.traceObject_schedule_eq_spine_schedule
    (object : TraceCorQObject) :
    object.schedule =
      (TraceAnalyticEffectiveRealization.traceObjectSpine object).schedule :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
