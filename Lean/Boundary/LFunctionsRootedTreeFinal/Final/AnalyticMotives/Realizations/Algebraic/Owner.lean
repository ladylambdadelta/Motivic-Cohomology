import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.TraceValue.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Soundness.Owner

/-!
# Algebraic realization

This directory owns the algebraic-facing realization of the trace computad.

At the current layer the realization is the representable/Yoneda interpretation
of typed trace correspondences.  Algebraic comparison data enters here from
algebraic motive and correspondence owner files, not from synthetic assumptions.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The algebraic Stokes-realization map is the Stokes by-kind representable map. -/
theorem TraceAlgebraicRealization.stokesMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.stokesMap_eq
    source
    target

/-- The algebraic residue-realization map is the residue by-kind representable map. -/
theorem TraceAlgebraicRealization.residueMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.residueMap_eq
    source
    target

/-- The algebraic channel-realization map is the channel by-kind representable map. -/
theorem TraceAlgebraicRealization.channelMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.channelMap_eq
    source
    target

/-- The algebraic refinement-realization map is the refinement by-kind representable map. -/
theorem TraceAlgebraicRealization.refinementMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.refinementMap_eq
    source
    target

/-- The algebraic schedule-realization map is the schedule by-kind representable map. -/
theorem TraceAlgebraicRealization.scheduleMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.scheduleMap_eq
    source
    target

/-- The algebraic weight-drop-realization map is the weight-drop by-kind representable map. -/
theorem TraceAlgebraicRealization.weightDropMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.weightDropMap_eq
    source
    target

/-- The algebraic Fubini-realization map is the Fubini by-kind representable map. -/
theorem TraceAlgebraicRealization.fubiniMap_eq_byKind
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.fubiniMap_eq
    source
    target

/-- The algebraic Stokes-realization map has the Stokes trace hom as preimage. -/
theorem TraceAlgebraicRealization.stokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAlgebraicSoundness.stokes_preimage
    source
    target

/-- The algebraic residue-realization map has the residue trace hom as preimage. -/
theorem TraceAlgebraicRealization.residueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAlgebraicSoundness.residue_preimage
    source
    target

/-- The algebraic channel-realization map has the channel trace hom as preimage. -/
theorem TraceAlgebraicRealization.channelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAlgebraicSoundness.channel_preimage
    source
    target

/-- The algebraic refinement-realization map has the refinement trace hom as preimage. -/
theorem TraceAlgebraicRealization.refinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAlgebraicSoundness.refinement_preimage
    source
    target

/-- The algebraic schedule-realization map has the schedule trace hom as preimage. -/
theorem TraceAlgebraicRealization.scheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAlgebraicSoundness.schedule_preimage
    source
    target

/-- The algebraic weight-drop-realization map has the weight-drop trace hom as preimage. -/
theorem TraceAlgebraicRealization.weightDropMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAlgebraicSoundness.weightDrop_preimage
    source
    target

/-- The algebraic Fubini-realization map has the Fubini trace hom as preimage. -/
theorem TraceAlgebraicRealization.fubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAlgebraicSoundness.fubini_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
