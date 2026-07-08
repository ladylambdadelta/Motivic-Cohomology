import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Comparison.Generators.Owner

/-!
# Comparison of realizations

This file collects the GAGA-style comparison target: analytic and algebraic
realizations of the same trace computad induce compatible Q-linear and motivic
calculus when their soundness chains are both available.

Comparison theorems in this lane sit after the analytic and algebraic
realization soundness chains.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The current realization comparison identifies analytic and algebraic Stokes maps. -/
theorem TraceRealizationComparison.currentStokesMapAgreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceAlgebraicRealizationGenerator.stokesMap source target :=
  TraceRealizationComparison.stokesMap_eq
    source
    target

/-- The current realization comparison identifies analytic and algebraic residue maps. -/
theorem TraceRealizationComparison.currentResidueMapAgreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceAlgebraicRealizationGenerator.residueMap source target :=
  TraceRealizationComparison.residueMap_eq
    source
    target

/-- The current realization comparison identifies analytic and algebraic channel maps. -/
theorem TraceRealizationComparison.currentChannelMapAgreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceAlgebraicRealizationGenerator.channelMap source target :=
  TraceRealizationComparison.channelMap_eq
    source
    target

/-- The current realization comparison identifies analytic and algebraic refinement maps. -/
theorem TraceRealizationComparison.currentRefinementMapAgreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceAlgebraicRealizationGenerator.refinementMap source target :=
  TraceRealizationComparison.refinementMap_eq
    source
    target

/-- The current realization comparison identifies analytic and algebraic schedule maps. -/
theorem TraceRealizationComparison.currentScheduleMapAgreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceAlgebraicRealizationGenerator.scheduleMap source target :=
  TraceRealizationComparison.scheduleMap_eq
    source
    target

/-- The current realization comparison identifies analytic and algebraic weight-drop maps. -/
theorem TraceRealizationComparison.currentWeightDropMapAgreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceAlgebraicRealizationGenerator.weightDropMap source target :=
  TraceRealizationComparison.weightDropMap_eq
    source
    target

/-- The current realization comparison identifies analytic and algebraic Fubini maps. -/
theorem TraceRealizationComparison.currentFubiniMapAgreement
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceAlgebraicRealizationGenerator.fubiniMap source target :=
  TraceRealizationComparison.fubiniMap_eq
    source
    target

/-- The current comparison Stokes map is the Stokes by-kind representable map. -/
theorem TraceRealizationComparison.currentStokesMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  TraceRealizationComparison.stokesMap_eq_byKind
    source
    target

/-- The current comparison residue map is the residue by-kind representable map. -/
theorem TraceRealizationComparison.currentResidueMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  TraceRealizationComparison.residueMap_eq_byKind
    source
    target

/-- The current comparison channel map is the channel by-kind representable map. -/
theorem TraceRealizationComparison.currentChannelMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  TraceRealizationComparison.channelMap_eq_byKind
    source
    target

/-- The current comparison refinement map is the refinement by-kind representable map. -/
theorem TraceRealizationComparison.currentRefinementMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  TraceRealizationComparison.refinementMap_eq_byKind
    source
    target

/-- The current comparison schedule map is the schedule by-kind representable map. -/
theorem TraceRealizationComparison.currentScheduleMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  TraceRealizationComparison.scheduleMap_eq_byKind
    source
    target

/-- The current comparison weight-drop map is the weight-drop by-kind representable map. -/
theorem TraceRealizationComparison.currentWeightDropMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  TraceRealizationComparison.weightDropMap_eq_byKind
    source
    target

/-- The current comparison Fubini map is the Fubini by-kind representable map. -/
theorem TraceRealizationComparison.currentFubiniMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  TraceRealizationComparison.fubiniMap_eq_byKind
    source
    target

/-- The current comparison Stokes map has the Stokes trace hom as preimage. -/
theorem TraceRealizationComparison.currentStokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceRealizationComparison.stokesMap_preimage
    source
    target

/-- The current comparison residue map has the residue trace hom as preimage. -/
theorem TraceRealizationComparison.currentResidueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceRealizationComparison.residueMap_preimage
    source
    target

/-- The current comparison channel map has the channel trace hom as preimage. -/
theorem TraceRealizationComparison.currentChannelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceRealizationComparison.channelMap_preimage
    source
    target

/-- The current comparison refinement map has the refinement trace hom as preimage. -/
theorem TraceRealizationComparison.currentRefinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceRealizationComparison.refinementMap_preimage
    source
    target

/-- The current comparison schedule map has the schedule trace hom as preimage. -/
theorem TraceRealizationComparison.currentScheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceRealizationComparison.scheduleMap_preimage
    source
    target

/-- The current comparison weight-drop map has the weight-drop trace hom as preimage. -/
theorem TraceRealizationComparison.currentWeightDropMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceRealizationComparison.weightDropMap_preimage
    source
    target

/-- The current comparison Fubini map has the Fubini trace hom as preimage. -/
theorem TraceRealizationComparison.currentFubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceRealizationComparison.fubiniMap_preimage
    source
    target

/-- The algebraic Stokes preimage currently agrees with the analytic Stokes preimage. -/
theorem TraceRealizationComparison.currentAlgebraicStokesPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.stokesMap source target) :=
  TraceRealizationComparison.algebraic_stokesMap_preimage_eq_analytic
    source
    target

/-- The algebraic residue preimage currently agrees with the analytic residue preimage. -/
theorem TraceRealizationComparison.currentAlgebraicResiduePreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) :=
  TraceRealizationComparison.algebraic_residueMap_preimage_eq_analytic
    source
    target

/-- The algebraic channel preimage currently agrees with the analytic channel preimage. -/
theorem TraceRealizationComparison.currentAlgebraicChannelPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.channelMap source target) :=
  TraceRealizationComparison.algebraic_channelMap_preimage_eq_analytic
    source
    target

/-- The algebraic refinement preimage currently agrees with the analytic refinement preimage. -/
theorem TraceRealizationComparison.currentAlgebraicRefinementPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.refinementMap source target) :=
  rfl

/-- The algebraic schedule preimage currently agrees with the analytic schedule preimage. -/
theorem TraceRealizationComparison.currentAlgebraicSchedulePreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.scheduleMap source target) :=
  rfl

/-- The algebraic weight-drop preimage currently agrees with the analytic weight-drop preimage. -/
theorem TraceRealizationComparison.currentAlgebraicWeightDropPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.weightDropMap source target) :=
  rfl

/-- The algebraic Fubini preimage currently agrees with the analytic Fubini preimage. -/
theorem TraceRealizationComparison.currentAlgebraicFubiniPreimage_eq_analytic
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.fubiniMap source target) :=
  TraceRealizationComparison.algebraic_fubiniMap_preimage_eq_analytic
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
