import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Comparison.ByKind.Owner

/-!
# Top-root analytic realization preimages
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes the Stokes trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonStokesGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticMotive.comparisonStokesGenerator_preimage
    source
    target

/-- The analytic-motives root exposes the residue trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonResidueGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticMotive.comparisonResidueGenerator_preimage
    source
    target

/-- The analytic-motives root exposes the channel trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonChannelGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticMotive.comparisonChannelGenerator_preimage
    source
    target

/-- The analytic-motives root exposes the refinement trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonRefinementGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticMotive.comparisonRefinementGenerator_preimage
    source
    target

/-- The analytic-motives root exposes the schedule trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonScheduleGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticMotive.comparisonScheduleGenerator_preimage
    source
    target

/-- The analytic-motives root exposes the weight-drop trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonWeightDropGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticMotive.comparisonWeightDropGenerator_preimage
    source
    target

/-- The analytic-motives root exposes the Fubini trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonFubiniGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticMotive.comparisonFubiniGenerator_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
