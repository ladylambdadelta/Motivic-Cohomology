import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Descent.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.IntervalHomotopy.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.TateStabilization.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Comparison.Generators.Owner

/-!
# Calculus generator inventory

This file owns the inventory of concrete representable-presheaf generator maps
currently exposed for the analytic-motives construction.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent channel generators are the underlying channel rewrite maps. -/
theorem TraceCalculusGenerator.descent_channel_eq_byKind
    (source target : QTraceExpression) :
    TraceDescentGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  rfl

/-- Descent refinement generators are the underlying refinement rewrite maps. -/
theorem TraceCalculusGenerator.descent_refinement_eq_byKind
    (source target : QTraceExpression) :
    TraceDescentGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  rfl

/-- Descent schedule generators are the underlying schedule rewrite maps. -/
theorem TraceCalculusGenerator.descent_schedule_eq_byKind
    (source target : QTraceExpression) :
    TraceDescentGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  rfl

/-- Interval-homotopy Stokes generators are the underlying Stokes rewrite maps. -/
theorem TraceCalculusGenerator.interval_stokes_eq_byKind
    (source target : QTraceExpression) :
    TraceIntervalHomotopyGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  rfl

/-- Interval-homotopy Fubini generators are the underlying Fubini rewrite maps. -/
theorem TraceCalculusGenerator.interval_fubini_eq_byKind
    (source target : QTraceExpression) :
    TraceIntervalHomotopyGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  rfl

/-- Tate-stabilization generators are the underlying weight-drop rewrite maps. -/
theorem TraceCalculusGenerator.tate_weightDrop_eq_byKind
    (source target : QTraceExpression) :
    TraceTateStabilizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  rfl

/-- Analytic realization residue generators are the underlying residue rewrite maps. -/
theorem TraceCalculusGenerator.analytic_residue_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  rfl

/-- Algebraic realization residue generators are the same underlying residue rewrite maps. -/
theorem TraceCalculusGenerator.algebraic_residue_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  rfl

/-- Analytic and algebraic residue generators agree at the inventory level. -/
theorem TraceCalculusGenerator.residue_realization_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceAlgebraicRealizationGenerator.residueMap source target :=
  TraceRealizationComparison.residueMap_eq source target

end AnalyticMotives
end LFunctions
end Boundary
