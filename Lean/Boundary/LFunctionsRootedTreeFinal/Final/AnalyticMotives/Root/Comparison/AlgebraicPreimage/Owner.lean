import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Comparison.PreimageAgreement.Owner

/-!
# Top-root algebraic realization preimages
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes the algebraic Stokes trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicStokesGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticMotive.comparisonAlgebraicStokesGenerator_preimage
    source
    target

/-- The analytic-motives root exposes the algebraic residue trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicResidueGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticMotive.comparisonAlgebraicResidueGenerator_preimage
    source
    target

/-- The analytic-motives root exposes the algebraic channel trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicChannelGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticMotive.comparisonAlgebraicChannelGenerator_preimage
    source
    target

/-- The analytic-motives root exposes the algebraic refinement trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicRefinementGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticMotive.comparisonAlgebraicRefinementGenerator_preimage
    source
    target

/-- The analytic-motives root exposes the algebraic schedule trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicScheduleGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticMotive.comparisonAlgebraicScheduleGenerator_preimage
    source
    target

/-- The analytic-motives root exposes the algebraic weight-drop trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicWeightDropGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticMotive.comparisonAlgebraicWeightDropGenerator_preimage
    source
    target

/-- The analytic-motives root exposes the algebraic Fubini trace-hom preimage. -/
theorem AnalyticMotivesRoot.comparisonAlgebraicFubiniGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticMotive.comparisonAlgebraicFubiniGenerator_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
