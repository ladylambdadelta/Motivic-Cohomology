import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Comparison.Owner

/-!
# Top-root analytic/algebraic comparison agreements
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes Stokes realization agreement. -/
theorem AnalyticMotivesRoot.comparisonStokesGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceAlgebraicRealizationGenerator.stokesMap source target :=
  TraceAnalyticMotive.comparisonStokesGenerator_agreement
    source
    target

/-- The analytic-motives root exposes residue realization agreement. -/
theorem AnalyticMotivesRoot.comparisonResidueGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceAlgebraicRealizationGenerator.residueMap source target :=
  TraceAnalyticMotive.comparisonResidueGenerator_agreement
    source
    target

/-- The analytic-motives root exposes channel realization agreement. -/
theorem AnalyticMotivesRoot.comparisonChannelGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceAlgebraicRealizationGenerator.channelMap source target :=
  TraceAnalyticMotive.comparisonChannelGenerator_agreement
    source
    target

/-- The analytic-motives root exposes refinement realization agreement. -/
theorem AnalyticMotivesRoot.comparisonRefinementGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceAlgebraicRealizationGenerator.refinementMap source target :=
  TraceAnalyticMotive.comparisonRefinementGenerator_agreement
    source
    target

/-- The analytic-motives root exposes schedule realization agreement. -/
theorem AnalyticMotivesRoot.comparisonScheduleGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceAlgebraicRealizationGenerator.scheduleMap source target :=
  TraceAnalyticMotive.comparisonScheduleGenerator_agreement
    source
    target

/-- The analytic-motives root exposes weight-drop realization agreement. -/
theorem AnalyticMotivesRoot.comparisonWeightDropGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceAlgebraicRealizationGenerator.weightDropMap source target :=
  TraceAnalyticMotive.comparisonWeightDropGenerator_agreement
    source
    target

/-- The analytic-motives root exposes Fubini realization agreement. -/
theorem AnalyticMotivesRoot.comparisonFubiniGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceAlgebraicRealizationGenerator.fubiniMap source target :=
  TraceAnalyticMotive.comparisonFubiniGenerator_agreement
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
