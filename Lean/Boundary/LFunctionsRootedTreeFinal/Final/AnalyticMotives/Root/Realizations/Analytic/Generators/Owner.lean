import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Generators.Owner

/-!
# Top-root analytic realization generators

This file exposes the generic analytic realization generator maps at the public
analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic Stokes realization map is the by-kind Stokes representable map. -/
theorem AnalyticMotivesRoot.analyticRealization_stokesMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.stokesMap_eq
    source
    target

/-- The analytic residue realization map is the by-kind residue representable map. -/
theorem AnalyticMotivesRoot.analyticRealization_residueMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.residueMap_eq
    source
    target

/-- The analytic channel realization map is the by-kind channel representable map. -/
theorem AnalyticMotivesRoot.analyticRealization_channelMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.channelMap_eq
    source
    target

/-- The analytic refinement realization map is the by-kind refinement representable map. -/
theorem AnalyticMotivesRoot.analyticRealization_refinementMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.refinementMap_eq
    source
    target

/-- The analytic schedule realization map is the by-kind schedule representable map. -/
theorem AnalyticMotivesRoot.analyticRealization_scheduleMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.scheduleMap_eq
    source
    target

/-- The analytic weight-drop realization map is the by-kind weight-drop representable map. -/
theorem AnalyticMotivesRoot.analyticRealization_weightDropMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.weightDropMap_eq
    source
    target

/-- The analytic Fubini realization map is the by-kind Fubini representable map. -/
theorem AnalyticMotivesRoot.analyticRealization_fubiniMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  TraceAnalyticRealizationGenerator.fubiniMap_eq
    source
    target

/-- The trace preimage of the analytic Stokes realization map is the Stokes trace hom. -/
theorem AnalyticMotivesRoot.analyticRealization_stokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticRealizationGenerator.stokesMap_preimage
    source
    target

/-- The trace preimage of the analytic residue realization map is the residue trace hom. -/
theorem AnalyticMotivesRoot.analyticRealization_residueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticRealizationGenerator.residueMap_preimage
    source
    target

/-- The trace preimage of the analytic channel realization map is the channel trace hom. -/
theorem AnalyticMotivesRoot.analyticRealization_channelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticRealizationGenerator.channelMap_preimage
    source
    target

/-- The trace preimage of the analytic refinement realization map is the refinement trace hom. -/
theorem AnalyticMotivesRoot.analyticRealization_refinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticRealizationGenerator.refinementMap_preimage
    source
    target

/-- The trace preimage of the analytic schedule realization map is the schedule trace hom. -/
theorem AnalyticMotivesRoot.analyticRealization_scheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticRealizationGenerator.scheduleMap_preimage
    source
    target

/-- The trace preimage of the analytic weight-drop realization map is the weight-drop trace hom. -/
theorem AnalyticMotivesRoot.analyticRealization_weightDropMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticRealizationGenerator.weightDropMap_preimage
    source
    target

/-- The trace preimage of the analytic Fubini realization map is the Fubini trace hom. -/
theorem AnalyticMotivesRoot.analyticRealization_fubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticRealizationGenerator.fubiniMap_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
