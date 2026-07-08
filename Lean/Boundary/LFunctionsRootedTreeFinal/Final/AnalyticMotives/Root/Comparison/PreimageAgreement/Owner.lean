import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Comparison.AnalyticPreimage.Owner

/-!
# Top-root algebraic and analytic preimage agreements
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes Stokes algebraic-vs-analytic preimage agreement. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicStokesPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) :=
  TraceAnalyticMotive.comparisonAlgebraicStokesPreimage_eq_analytic
    source
    target

/-- The analytic-motives root exposes residue algebraic-vs-analytic preimage agreement. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicResiduePreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) :=
  TraceAnalyticMotive.comparisonAlgebraicResiduePreimage_eq_analytic
    source
    target

/-- The analytic-motives root exposes channel algebraic-vs-analytic preimage agreement. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicChannelPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) :=
  TraceAnalyticMotive.comparisonAlgebraicChannelPreimage_eq_analytic
    source
    target

/-- The analytic-motives root exposes refinement algebraic-vs-analytic preimage agreement. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicRefinementPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) :=
  TraceAnalyticMotive.comparisonAlgebraicRefinementPreimage_eq_analytic
    source
    target

/-- The analytic-motives root exposes schedule algebraic-vs-analytic preimage agreement. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicSchedulePreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) :=
  TraceAnalyticMotive.comparisonAlgebraicSchedulePreimage_eq_analytic
    source
    target

/-- The analytic-motives root exposes weight-drop algebraic-vs-analytic preimage agreement. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicWeightDropPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) :=
  TraceAnalyticMotive.comparisonAlgebraicWeightDropPreimage_eq_analytic
    source
    target

/-- The analytic-motives root exposes Fubini algebraic-vs-analytic preimage agreement. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicFubiniPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) :=
  TraceAnalyticMotive.comparisonAlgebraicFubiniPreimage_eq_analytic
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
