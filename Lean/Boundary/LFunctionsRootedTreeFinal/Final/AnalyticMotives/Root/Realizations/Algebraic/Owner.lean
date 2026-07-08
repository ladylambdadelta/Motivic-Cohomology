import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Realizations.Algebraic.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Realizations.Algebraic.Soundness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Realizations.Algebraic.TraceValue.Owner

/-!
# Top-root algebraic realization facade

This file collects public root facades for algebraic realization data.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Algebraic realization aggregate: Stokes maps are the by-kind representable maps. -/
theorem AnalyticMotivesRoot.algebraicRealizationSummary_stokesMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  AnalyticMotivesRoot.algebraicRealization_stokesMap_eq
    source
    target

/-- Algebraic realization aggregate: Fubini maps are the by-kind representable maps. -/
theorem AnalyticMotivesRoot.algebraicRealizationSummary_fubiniMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  AnalyticMotivesRoot.algebraicRealization_fubiniMap_eq
    source
    target

/-- Algebraic realization aggregate: Stokes realization preimage is the Stokes trace hom. -/
theorem AnalyticMotivesRoot.algebraicRealizationSummary_stokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  AnalyticMotivesRoot.algebraicRealization_stokesMap_preimage
    source
    target

/-- Algebraic realization aggregate: Fubini realization preimage is the Fubini trace hom. -/
theorem AnalyticMotivesRoot.algebraicRealizationSummary_fubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  AnalyticMotivesRoot.algebraicRealization_fubiniMap_preimage
    source
    target

/-- Algebraic realization aggregate: trace-value modules are representable sections. -/
theorem AnalyticMotivesRoot.algebraicRealizationSummary_module_eq_representable_sections
    (source target : TraceCorQObject) :
    AlgebraicTraceValue.module source target =
      (TraceCorQPresheaf.representable target).sections source :=
  AnalyticMotivesRoot.algebraicTraceValue_module_eq_representable_sections
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
