import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Realizations.Analytic.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Realizations.Analytic.TraceValue.Owner

/-!
# Top-root analytic realization facade

This file collects public root facades for analytic realization data.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Analytic realization aggregate: Stokes maps are the by-kind representable maps. -/
theorem AnalyticMotivesRoot.analyticRealizationSummary_stokesMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  AnalyticMotivesRoot.analyticRealization_stokesMap_eq
    source
    target

/-- Analytic realization aggregate: Fubini maps are the by-kind representable maps. -/
theorem AnalyticMotivesRoot.analyticRealizationSummary_fubiniMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  AnalyticMotivesRoot.analyticRealization_fubiniMap_eq
    source
    target

/-- Analytic realization aggregate: Stokes realization preimage is the Stokes trace hom. -/
theorem AnalyticMotivesRoot.analyticRealizationSummary_stokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  AnalyticMotivesRoot.analyticRealization_stokesMap_preimage
    source
    target

/-- Analytic realization aggregate: Fubini realization preimage is the Fubini trace hom. -/
theorem AnalyticMotivesRoot.analyticRealizationSummary_fubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  AnalyticMotivesRoot.analyticRealization_fubiniMap_preimage
    source
    target

/-- Analytic realization aggregate: channel decomposition is right plus horizontal minus boundary. -/
theorem AnalyticMotivesRoot.analyticRealizationSummary_channelDecomposition_eq
    (right horizontal boundary : AnalyticTraceValue) :
    AnalyticTraceValue.channelDecomposition
        right
        horizontal
        boundary =
      right + horizontal - boundary :=
  AnalyticMotivesRoot.analyticTraceValue_channelDecomposition_eq
    right
    horizontal
    boundary

end AnalyticMotives
end LFunctions
end Boundary
