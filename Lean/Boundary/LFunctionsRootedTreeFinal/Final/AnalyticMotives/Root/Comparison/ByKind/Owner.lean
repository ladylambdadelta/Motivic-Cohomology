import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Comparison.Agreement.Owner

/-!
# Top-root comparison by-kind identifications
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes the common Stokes by-kind map. -/
theorem AnalyticMotivesRoot.comparisonStokesGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  TraceAnalyticMotive.comparisonStokesGenerator_eq_byKind
    source
    target

/-- The analytic-motives root exposes the common residue by-kind map. -/
theorem AnalyticMotivesRoot.comparisonResidueGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  TraceAnalyticMotive.comparisonResidueGenerator_eq_byKind
    source
    target

/-- The analytic-motives root exposes the common channel by-kind map. -/
theorem AnalyticMotivesRoot.comparisonChannelGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  TraceAnalyticMotive.comparisonChannelGenerator_eq_byKind
    source
    target

/-- The analytic-motives root exposes the common refinement by-kind map. -/
theorem AnalyticMotivesRoot.comparisonRefinementGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  TraceAnalyticMotive.comparisonRefinementGenerator_eq_byKind
    source
    target

/-- The analytic-motives root exposes the common schedule by-kind map. -/
theorem AnalyticMotivesRoot.comparisonScheduleGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  TraceAnalyticMotive.comparisonScheduleGenerator_eq_byKind
    source
    target

/-- The analytic-motives root exposes the common weight-drop by-kind map. -/
theorem AnalyticMotivesRoot.comparisonWeightDropGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  TraceAnalyticMotive.comparisonWeightDropGenerator_eq_byKind
    source
    target

/-- The analytic-motives root exposes the common Fubini by-kind map. -/
theorem AnalyticMotivesRoot.comparisonFubiniGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  TraceAnalyticMotive.comparisonFubiniGenerator_eq_byKind
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
