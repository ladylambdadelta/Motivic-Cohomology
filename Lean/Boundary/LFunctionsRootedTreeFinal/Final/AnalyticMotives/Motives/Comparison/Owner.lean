import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Comparison.Summary.Owner

/-!
# Comparison with geometric motives

This file collects the comparison lane between compact analytic motives and
geometric motives over a perfect field, especially the rational comparison with
`DM_gm(Q)_Q`.

Comparison statements in this lane are downstream of the trace-correspondence
presentation, the stable analytic Verdier quotient, the concrete analytic
weight profile, the analytic effective-realization endpoint surfaces, and the
stable-recognition and weight-triangular projection surfaces toward the
geometric owner files already in the parent project.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-level comparison currently identifies analytic and algebraic Stokes generators. -/
theorem TraceAnalyticMotiveComparison.stokesGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceAlgebraicRealizationGenerator.stokesMap source target :=
  TraceRealizationComparison.currentStokesMapAgreement
    source
    target

/-- Motive-level comparison currently identifies analytic and algebraic residue generators. -/
theorem TraceAnalyticMotiveComparison.residueGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceAlgebraicRealizationGenerator.residueMap source target :=
  TraceCalculusGenerator.residue_realization_agreement
    source
    target

/-- Motive-level comparison currently identifies analytic and algebraic channel generators. -/
theorem TraceAnalyticMotiveComparison.channelGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceAlgebraicRealizationGenerator.channelMap source target :=
  TraceRealizationComparison.currentChannelMapAgreement
    source
    target

/-- Motive-level comparison currently identifies analytic and algebraic refinement generators. -/
theorem TraceAnalyticMotiveComparison.refinementGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceAlgebraicRealizationGenerator.refinementMap source target :=
  TraceRealizationComparison.currentRefinementMapAgreement
    source
    target

/-- Motive-level comparison currently identifies analytic and algebraic schedule generators. -/
theorem TraceAnalyticMotiveComparison.scheduleGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceAlgebraicRealizationGenerator.scheduleMap source target :=
  TraceRealizationComparison.currentScheduleMapAgreement
    source
    target

/-- Motive-level comparison currently identifies analytic and algebraic weight-drop generators. -/
theorem TraceAnalyticMotiveComparison.weightDropGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceAlgebraicRealizationGenerator.weightDropMap source target :=
  TraceRealizationComparison.currentWeightDropMapAgreement
    source
    target

/-- Motive-level comparison currently identifies analytic and algebraic Fubini generators. -/
theorem TraceAnalyticMotiveComparison.fubiniGenerator_agreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceAlgebraicRealizationGenerator.fubiniMap source target :=
  TraceRealizationComparison.currentFubiniMapAgreement
    source
    target

/-- The common comparison Stokes generator is the Stokes rewrite map. -/
theorem TraceAnalyticMotiveComparison.stokesGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  TraceRealizationComparison.currentStokesMap_eq_byKind
    source
    target

/-- The common comparison residue generator is the residue rewrite map. -/
theorem TraceAnalyticMotiveComparison.residueGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  TraceRealizationComparison.currentResidueMap_eq_byKind
    source
    target

/-- The common comparison channel generator is the channel rewrite map. -/
theorem TraceAnalyticMotiveComparison.channelGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  TraceRealizationComparison.currentChannelMap_eq_byKind
    source
    target

/-- The common comparison refinement generator is the refinement rewrite map. -/
theorem TraceAnalyticMotiveComparison.refinementGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  TraceRealizationComparison.currentRefinementMap_eq_byKind
    source
    target

/-- The common comparison schedule generator is the schedule rewrite map. -/
theorem TraceAnalyticMotiveComparison.scheduleGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  TraceRealizationComparison.currentScheduleMap_eq_byKind
    source
    target

/-- The common comparison weight-drop generator is the weight-drop rewrite map. -/
theorem TraceAnalyticMotiveComparison.weightDropGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  TraceRealizationComparison.currentWeightDropMap_eq_byKind
    source
    target

/-- The common comparison Fubini generator is the Fubini rewrite map. -/
theorem TraceAnalyticMotiveComparison.fubiniGenerator_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  TraceRealizationComparison.currentFubiniMap_eq_byKind
    source
    target

/-- The motive-level comparison Stokes generator has the Stokes trace hom as preimage. -/
theorem TraceAnalyticMotiveComparison.stokesGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceRealizationComparison.currentStokesMap_preimage
    source
    target

/-- The motive-level comparison residue generator has the residue trace hom as preimage. -/
theorem TraceAnalyticMotiveComparison.residueGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceRealizationComparison.currentResidueMap_preimage
    source
    target

/-- The motive-level comparison channel generator has the channel trace hom as preimage. -/
theorem TraceAnalyticMotiveComparison.channelGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceRealizationComparison.currentChannelMap_preimage
    source
    target

/-- The motive-level comparison refinement generator has the refinement trace hom as preimage. -/
theorem TraceAnalyticMotiveComparison.refinementGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceRealizationComparison.currentRefinementMap_preimage
    source
    target

/-- The motive-level comparison schedule generator has the schedule trace hom as preimage. -/
theorem TraceAnalyticMotiveComparison.scheduleGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceRealizationComparison.currentScheduleMap_preimage
    source
    target

/-- The motive-level comparison weight-drop generator has the weight-drop trace hom as preimage. -/
theorem TraceAnalyticMotiveComparison.weightDropGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceRealizationComparison.currentWeightDropMap_preimage
    source
    target

/-- The motive-level comparison Fubini generator has the Fubini trace hom as preimage. -/
theorem TraceAnalyticMotiveComparison.fubiniGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceRealizationComparison.currentFubiniMap_preimage
    source
    target

/-- Algebraic and analytic Stokes preimages agree in the motive comparison lane. -/
theorem TraceAnalyticMotiveComparison.algebraicStokesPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) :=
  TraceRealizationComparison.currentAlgebraicStokesPreimage_eq_analytic
    source
    target

/-- Algebraic and analytic residue preimages agree in the motive comparison lane. -/
theorem TraceAnalyticMotiveComparison.algebraicResiduePreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) :=
  TraceRealizationComparison.currentAlgebraicResiduePreimage_eq_analytic
    source
    target

/-- Algebraic and analytic channel preimages agree in the motive comparison lane. -/
theorem TraceAnalyticMotiveComparison.algebraicChannelPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) :=
  TraceRealizationComparison.currentAlgebraicChannelPreimage_eq_analytic
    source
    target

/-- Algebraic and analytic refinement preimages agree in the motive comparison lane. -/
theorem TraceAnalyticMotiveComparison.algebraicRefinementPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) :=
  TraceRealizationComparison.currentAlgebraicRefinementPreimage_eq_analytic
    source
    target

/-- Algebraic and analytic schedule preimages agree in the motive comparison lane. -/
theorem TraceAnalyticMotiveComparison.algebraicSchedulePreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) :=
  TraceRealizationComparison.currentAlgebraicSchedulePreimage_eq_analytic
    source
    target

/-- Algebraic and analytic weight-drop preimages agree in the motive comparison lane. -/
theorem TraceAnalyticMotiveComparison.algebraicWeightDropPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) :=
  TraceRealizationComparison.currentAlgebraicWeightDropPreimage_eq_analytic
    source
    target

/-- Algebraic and analytic Fubini preimages agree in the motive comparison lane. -/
theorem TraceAnalyticMotiveComparison.algebraicFubiniPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) :=
  TraceRealizationComparison.currentAlgebraicFubiniPreimage_eq_analytic
    source
    target

/-- The algebraic Stokes generator has the same Stokes trace-hom preimage. -/
theorem TraceAnalyticMotiveComparison.algebraicStokesGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  Eq.trans
    (TraceAnalyticMotiveComparison.algebraicStokesPreimage_eq_analytic
      source
      target)
    (TraceAnalyticMotiveComparison.stokesGenerator_preimage
      source
      target)

/-- The algebraic residue generator has the same residue trace-hom preimage. -/
theorem TraceAnalyticMotiveComparison.algebraicResidueGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  Eq.trans
    (TraceAnalyticMotiveComparison.algebraicResiduePreimage_eq_analytic
      source
      target)
    (TraceAnalyticMotiveComparison.residueGenerator_preimage
      source
      target)

/-- The algebraic channel generator has the same channel trace-hom preimage. -/
theorem TraceAnalyticMotiveComparison.algebraicChannelGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  Eq.trans
    (TraceAnalyticMotiveComparison.algebraicChannelPreimage_eq_analytic
      source
      target)
    (TraceAnalyticMotiveComparison.channelGenerator_preimage
      source
      target)

/-- The algebraic refinement generator has the same refinement trace-hom preimage. -/
theorem TraceAnalyticMotiveComparison.algebraicRefinementGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  Eq.trans
    (TraceAnalyticMotiveComparison.algebraicRefinementPreimage_eq_analytic
      source
      target)
    (TraceAnalyticMotiveComparison.refinementGenerator_preimage
      source
      target)

/-- The algebraic schedule generator has the same schedule trace-hom preimage. -/
theorem TraceAnalyticMotiveComparison.algebraicScheduleGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  Eq.trans
    (TraceAnalyticMotiveComparison.algebraicSchedulePreimage_eq_analytic
      source
      target)
    (TraceAnalyticMotiveComparison.scheduleGenerator_preimage
      source
      target)

/-- The algebraic weight-drop generator has the same weight-drop trace-hom preimage. -/
theorem TraceAnalyticMotiveComparison.algebraicWeightDropGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  Eq.trans
    (TraceAnalyticMotiveComparison.algebraicWeightDropPreimage_eq_analytic
      source
      target)
    (TraceAnalyticMotiveComparison.weightDropGenerator_preimage
      source
      target)

/-- The algebraic Fubini generator has the same Fubini trace-hom preimage. -/
theorem TraceAnalyticMotiveComparison.algebraicFubiniGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  Eq.trans
    (TraceAnalyticMotiveComparison.algebraicFubiniPreimage_eq_analytic
      source
      target)
    (TraceAnalyticMotiveComparison.fubiniGenerator_preimage
      source
      target)

end AnalyticMotives
end LFunctions
end Boundary
