import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Generators.Owner

/-!
# Generator-level comparison of realizations

This file owns the first comparison layer between analytic and algebraic
realization generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Analytic and algebraic residue generator maps are the same representable map. -/
theorem TraceRealizationComparison.residueMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceAlgebraicRealizationGenerator.residueMap source target :=
  rfl

/-- The common residue generator map is the by-kind residue representable map. -/
theorem TraceRealizationComparison.residueMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  rfl

/-- The common residue generator map has the residue trace hom as trace preimage. -/
theorem TraceRealizationComparison.residueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticRealizationGenerator.residueMap_preimage source target

/-- Algebraic residue preimage agrees with analytic residue preimage. -/
theorem TraceRealizationComparison.algebraic_residueMap_preimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
