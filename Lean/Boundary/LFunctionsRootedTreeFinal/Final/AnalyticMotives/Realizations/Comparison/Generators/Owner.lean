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

/-- Analytic and algebraic Stokes generator maps are the same representable map. -/
theorem TraceRealizationComparison.stokesMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceAlgebraicRealizationGenerator.stokesMap source target :=
  rfl

/-- Analytic and algebraic residue generator maps are the same representable map. -/
theorem TraceRealizationComparison.residueMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceAlgebraicRealizationGenerator.residueMap source target :=
  rfl

/-- Analytic and algebraic channel generator maps are the same representable map. -/
theorem TraceRealizationComparison.channelMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceAlgebraicRealizationGenerator.channelMap source target :=
  rfl

/-- Analytic and algebraic refinement generator maps are the same representable map. -/
theorem TraceRealizationComparison.refinementMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceAlgebraicRealizationGenerator.refinementMap source target :=
  rfl

/-- Analytic and algebraic schedule generator maps are the same representable map. -/
theorem TraceRealizationComparison.scheduleMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceAlgebraicRealizationGenerator.scheduleMap source target :=
  rfl

/-- Analytic and algebraic weight-drop generator maps are the same representable map. -/
theorem TraceRealizationComparison.weightDropMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceAlgebraicRealizationGenerator.weightDropMap source target :=
  rfl

/-- Analytic and algebraic Fubini generator maps are the same representable map. -/
theorem TraceRealizationComparison.fubiniMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceAlgebraicRealizationGenerator.fubiniMap source target :=
  rfl

/-- The common Stokes generator map is the by-kind Stokes representable map. -/
theorem TraceRealizationComparison.stokesMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  rfl

/-- The common residue generator map is the by-kind residue representable map. -/
theorem TraceRealizationComparison.residueMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  rfl

/-- The common channel generator map is the by-kind channel representable map. -/
theorem TraceRealizationComparison.channelMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  rfl

/-- The common refinement generator map is the by-kind refinement representable map. -/
theorem TraceRealizationComparison.refinementMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  rfl

/-- The common schedule generator map is the by-kind schedule representable map. -/
theorem TraceRealizationComparison.scheduleMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  rfl

/-- The common weight-drop generator map is the by-kind weight-drop representable map. -/
theorem TraceRealizationComparison.weightDropMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  rfl

/-- The common Fubini generator map is the by-kind Fubini representable map. -/
theorem TraceRealizationComparison.fubiniMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  rfl

/-- The common Stokes generator map has the Stokes trace hom as trace preimage. -/
theorem TraceRealizationComparison.stokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticRealizationGenerator.stokesMap_preimage source target

/-- The common residue generator map has the residue trace hom as trace preimage. -/
theorem TraceRealizationComparison.residueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticRealizationGenerator.residueMap_preimage source target

/-- The common channel generator map has the channel trace hom as trace preimage. -/
theorem TraceRealizationComparison.channelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticRealizationGenerator.channelMap_preimage source target

/-- The common refinement generator map has the refinement trace hom as trace preimage. -/
theorem TraceRealizationComparison.refinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticRealizationGenerator.refinementMap_preimage source target

/-- The common schedule generator map has the schedule trace hom as trace preimage. -/
theorem TraceRealizationComparison.scheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticRealizationGenerator.scheduleMap_preimage source target

/-- The common weight-drop generator map has the weight-drop trace hom as trace preimage. -/
theorem TraceRealizationComparison.weightDropMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticRealizationGenerator.weightDropMap_preimage source target

/-- The common Fubini generator map has the Fubini trace hom as trace preimage. -/
theorem TraceRealizationComparison.fubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticRealizationGenerator.fubiniMap_preimage source target

/-- Algebraic Stokes preimage agrees with analytic Stokes preimage. -/
theorem TraceRealizationComparison.algebraic_stokesMap_preimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) :=
  rfl

/-- Algebraic residue preimage agrees with analytic residue preimage. -/
theorem TraceRealizationComparison.algebraic_residueMap_preimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) :=
  rfl

/-- Algebraic channel preimage agrees with analytic channel preimage. -/
theorem TraceRealizationComparison.algebraic_channelMap_preimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) :=
  rfl

/-- Algebraic Fubini preimage agrees with analytic Fubini preimage. -/
theorem TraceRealizationComparison.algebraic_fubiniMap_preimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
