import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Generators.Owner

/-!
# Top-root algebraic realization generators

This file exposes the generic algebraic realization generator maps at the public
analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The algebraic Stokes realization map is the by-kind Stokes representable map. -/
theorem AnalyticMotivesRoot.algebraicRealization_stokesMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.stokesMap_eq
    source
    target

/-- The algebraic residue realization map is the by-kind residue representable map. -/
theorem AnalyticMotivesRoot.algebraicRealization_residueMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.residueMap_eq
    source
    target

/-- The algebraic channel realization map is the by-kind channel representable map. -/
theorem AnalyticMotivesRoot.algebraicRealization_channelMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.channelMap_eq
    source
    target

/-- The algebraic refinement realization map is the by-kind refinement representable map. -/
theorem AnalyticMotivesRoot.algebraicRealization_refinementMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.refinementMap_eq
    source
    target

/-- The algebraic schedule realization map is the by-kind schedule representable map. -/
theorem AnalyticMotivesRoot.algebraicRealization_scheduleMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.scheduleMap_eq
    source
    target

/-- The algebraic weight-drop realization map is the by-kind weight-drop representable map. -/
theorem AnalyticMotivesRoot.algebraicRealization_weightDropMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.weightDropMap_eq
    source
    target

/-- The algebraic Fubini realization map is the by-kind Fubini representable map. -/
theorem AnalyticMotivesRoot.algebraicRealization_fubiniMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  TraceAlgebraicRealizationGenerator.fubiniMap_eq
    source
    target

/-- The trace preimage of the algebraic Stokes realization map is the Stokes trace hom. -/
theorem AnalyticMotivesRoot.algebraicRealization_stokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAlgebraicRealizationGenerator.stokesMap_preimage
    source
    target

/-- The trace preimage of the algebraic residue realization map is the residue trace hom. -/
theorem AnalyticMotivesRoot.algebraicRealization_residueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAlgebraicRealizationGenerator.residueMap_preimage
    source
    target

/-- The trace preimage of the algebraic channel realization map is the channel trace hom. -/
theorem AnalyticMotivesRoot.algebraicRealization_channelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAlgebraicRealizationGenerator.channelMap_preimage
    source
    target

/-- The trace preimage of the algebraic refinement realization map is the refinement trace hom. -/
theorem AnalyticMotivesRoot.algebraicRealization_refinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAlgebraicRealizationGenerator.refinementMap_preimage
    source
    target

/-- The trace preimage of the algebraic schedule realization map is the schedule trace hom. -/
theorem AnalyticMotivesRoot.algebraicRealization_scheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAlgebraicRealizationGenerator.scheduleMap_preimage
    source
    target

/-- The trace preimage of the algebraic weight-drop realization map is the weight-drop trace hom. -/
theorem AnalyticMotivesRoot.algebraicRealization_weightDropMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAlgebraicRealizationGenerator.weightDropMap_preimage
    source
    target

/-- The trace preimage of the algebraic Fubini realization map is the Fubini trace hom. -/
theorem AnalyticMotivesRoot.algebraicRealization_fubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAlgebraicRealizationGenerator.fubiniMap_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
