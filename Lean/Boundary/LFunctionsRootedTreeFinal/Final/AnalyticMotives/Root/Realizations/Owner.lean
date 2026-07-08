import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Realizations.Analytic.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Realizations.Algebraic.Owner

/-!
# Top-root realization facade

This file collects public root facades for analytic and algebraic realization
generator maps.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Realization aggregate: analytic and algebraic Stokes realizations have the same trace preimage. -/
theorem AnalyticMotivesRoot.realizationSummary_stokes_preimage_agreement
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) :=
  Eq.trans
    (AnalyticMotivesRoot.analyticRealizationSummary_stokesMap_preimage
      source
      target)
    (Eq.symm
      (AnalyticMotivesRoot.algebraicRealizationSummary_stokesMap_preimage
        source
        target))

/-- Realization aggregate: analytic and algebraic Fubini realizations have the same trace preimage. -/
theorem AnalyticMotivesRoot.realizationSummary_fubini_preimage_agreement
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) :=
  Eq.trans
    (AnalyticMotivesRoot.analyticRealizationSummary_fubiniMap_preimage
      source
      target)
    (Eq.symm
      (AnalyticMotivesRoot.algebraicRealizationSummary_fubiniMap_preimage
        source
        target))

/-- Realization aggregate: analytic Stokes realization is the common Stokes representable map. -/
theorem AnalyticMotivesRoot.realizationSummary_analytic_stokesMap_common
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  AnalyticMotivesRoot.analyticRealizationSummary_stokesMap_eq
    source
    target

/-- Realization aggregate: algebraic Stokes realization is the common Stokes representable map. -/
theorem AnalyticMotivesRoot.realizationSummary_algebraic_stokesMap_common
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  AnalyticMotivesRoot.algebraicRealizationSummary_stokesMap_eq
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
