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

/-- Analytic realization Stokes generators are the underlying Stokes rewrite maps. -/
theorem TraceCalculusGenerator.analytic_stokes_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  rfl

/-- Analytic realization residue generators are the underlying residue rewrite maps. -/
theorem TraceCalculusGenerator.analytic_residue_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  rfl

/-- Analytic realization channel generators are the underlying channel rewrite maps. -/
theorem TraceCalculusGenerator.analytic_channel_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  rfl

/-- Analytic realization refinement generators are the underlying refinement rewrite maps. -/
theorem TraceCalculusGenerator.analytic_refinement_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  rfl

/-- Analytic realization schedule generators are the underlying schedule rewrite maps. -/
theorem TraceCalculusGenerator.analytic_schedule_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  rfl

/-- Analytic realization weight-drop generators are the underlying weight-drop rewrite maps. -/
theorem TraceCalculusGenerator.analytic_weightDrop_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  rfl

/-- Analytic realization Fubini generators are the underlying Fubini rewrite maps. -/
theorem TraceCalculusGenerator.analytic_fubini_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  rfl

/-- Algebraic realization Stokes generators are the same underlying Stokes rewrite maps. -/
theorem TraceCalculusGenerator.algebraic_stokes_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  rfl

/-- Algebraic realization residue generators are the same underlying residue rewrite maps. -/
theorem TraceCalculusGenerator.algebraic_residue_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  rfl

/-- Algebraic realization channel generators are the same underlying channel rewrite maps. -/
theorem TraceCalculusGenerator.algebraic_channel_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  rfl

/-- Algebraic realization refinement generators are the same underlying refinement rewrite maps. -/
theorem TraceCalculusGenerator.algebraic_refinement_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  rfl

/-- Algebraic realization schedule generators are the same underlying schedule rewrite maps. -/
theorem TraceCalculusGenerator.algebraic_schedule_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  rfl

/-- Algebraic realization weight-drop generators are the same underlying weight-drop rewrite maps. -/
theorem TraceCalculusGenerator.algebraic_weightDrop_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  rfl

/-- Algebraic realization Fubini generators are the same underlying Fubini rewrite maps. -/
theorem TraceCalculusGenerator.algebraic_fubini_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  rfl

/-- Analytic and algebraic Stokes generators agree at the inventory level. -/
theorem TraceCalculusGenerator.stokes_realization_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceAlgebraicRealizationGenerator.stokesMap source target :=
  TraceRealizationComparison.stokesMap_eq source target

/-- Analytic and algebraic residue generators agree at the inventory level. -/
theorem TraceCalculusGenerator.residue_realization_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceAlgebraicRealizationGenerator.residueMap source target :=
  TraceRealizationComparison.residueMap_eq source target

/-- Analytic and algebraic channel generators agree at the inventory level. -/
theorem TraceCalculusGenerator.channel_realization_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceAlgebraicRealizationGenerator.channelMap source target :=
  TraceRealizationComparison.channelMap_eq source target

/-- Analytic and algebraic refinement generators agree at the inventory level. -/
theorem TraceCalculusGenerator.refinement_realization_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceAlgebraicRealizationGenerator.refinementMap source target :=
  TraceRealizationComparison.refinementMap_eq source target

/-- Analytic and algebraic schedule generators agree at the inventory level. -/
theorem TraceCalculusGenerator.schedule_realization_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceAlgebraicRealizationGenerator.scheduleMap source target :=
  TraceRealizationComparison.scheduleMap_eq source target

/-- Analytic and algebraic weight-drop generators agree at the inventory level. -/
theorem TraceCalculusGenerator.weightDrop_realization_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceAlgebraicRealizationGenerator.weightDropMap source target :=
  TraceRealizationComparison.weightDropMap_eq source target

/-- Analytic and algebraic Fubini generators agree at the inventory level. -/
theorem TraceCalculusGenerator.fubini_realization_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceAlgebraicRealizationGenerator.fubiniMap source target :=
  TraceRealizationComparison.fubiniMap_eq source target

end AnalyticMotives
end LFunctions
end Boundary
