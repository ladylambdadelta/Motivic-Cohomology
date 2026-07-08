import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.RewriteMaps.ByKind.Maps.Owner

/-!
# Algebraic realization generator maps

This file owns concrete representable-presheaf maps used by the algebraic
realization layer before any comparison theorem is stated.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Stokes map used by the algebraic trace-value realization. -/
def TraceAlgebraicRealizationGenerator.stokesMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.stokes source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.stokes source target).targetObject) :=
  TraceRewriteGenerator.stokesRepresentableMap source target

/-- A residue-extraction map used by the algebraic trace-value realization. -/
def TraceAlgebraicRealizationGenerator.residueMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.residue source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.residue source target).targetObject) :=
  TraceRewriteGenerator.residueRepresentableMap source target

/-- A channel-decomposition map used by the algebraic trace-value realization. -/
def TraceAlgebraicRealizationGenerator.channelMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.channel source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.channel source target).targetObject) :=
  TraceRewriteGenerator.channelRepresentableMap source target

/-- A refinement-invariance map used by the algebraic trace-value realization. -/
def TraceAlgebraicRealizationGenerator.refinementMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.refinement source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.refinement source target).targetObject) :=
  TraceRewriteGenerator.refinementRepresentableMap source target

/-- A schedule-exchange map used by the algebraic trace-value realization. -/
def TraceAlgebraicRealizationGenerator.scheduleMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.schedule source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.schedule source target).targetObject) :=
  TraceRewriteGenerator.scheduleRepresentableMap source target

/-- A weight-drop map used by the algebraic trace-value realization. -/
def TraceAlgebraicRealizationGenerator.weightDropMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.weightDrop source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.weightDrop source target).targetObject) :=
  TraceRewriteGenerator.weightDropRepresentableMap source target

/-- A Fubini-interchange map used by the algebraic trace-value realization. -/
def TraceAlgebraicRealizationGenerator.fubiniMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.fubini source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.fubini source target).targetObject) :=
  TraceRewriteGenerator.fubiniRepresentableMap source target

/-- The algebraic realization Stokes map is the by-kind Stokes representable map. -/
theorem TraceAlgebraicRealizationGenerator.stokesMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  rfl

/-- The algebraic realization residue map is the by-kind residue representable map. -/
theorem TraceAlgebraicRealizationGenerator.residueMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  rfl

/-- The algebraic realization channel map is the by-kind channel representable map. -/
theorem TraceAlgebraicRealizationGenerator.channelMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.channelMap source target =
      TraceRewriteGenerator.channelRepresentableMap source target :=
  rfl

/-- The algebraic realization refinement map is the by-kind refinement representable map. -/
theorem TraceAlgebraicRealizationGenerator.refinementMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.refinementMap source target =
      TraceRewriteGenerator.refinementRepresentableMap source target :=
  rfl

/-- The algebraic realization schedule map is the by-kind schedule representable map. -/
theorem TraceAlgebraicRealizationGenerator.scheduleMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.scheduleMap source target =
      TraceRewriteGenerator.scheduleRepresentableMap source target :=
  rfl

/-- The algebraic realization weight-drop map is the by-kind weight-drop representable map. -/
theorem TraceAlgebraicRealizationGenerator.weightDropMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.weightDropMap source target =
      TraceRewriteGenerator.weightDropRepresentableMap source target :=
  rfl

/-- The algebraic realization Fubini map is the by-kind Fubini representable map. -/
theorem TraceAlgebraicRealizationGenerator.fubiniMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  rfl

/-- The trace preimage of an algebraic realization Stokes map is the Stokes trace hom. -/
theorem TraceAlgebraicRealizationGenerator.stokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.stokes source target)

/-- The trace preimage of an algebraic realization residue map is the residue trace hom. -/
theorem TraceAlgebraicRealizationGenerator.residueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.residue source target)

/-- The trace preimage of an algebraic realization channel map is the channel trace hom. -/
theorem TraceAlgebraicRealizationGenerator.channelMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.channel source target)

/-- The trace preimage of an algebraic realization refinement map is the refinement trace hom. -/
theorem TraceAlgebraicRealizationGenerator.refinementMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.refinement source target)

/-- The trace preimage of an algebraic realization schedule map is the schedule trace hom. -/
theorem TraceAlgebraicRealizationGenerator.scheduleMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.schedule source target)

/-- The trace preimage of an algebraic realization weight-drop map is the weight-drop trace hom. -/
theorem TraceAlgebraicRealizationGenerator.weightDropMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.weightDrop source target)

/-- The trace preimage of an algebraic realization Fubini map is the Fubini trace hom. -/
theorem TraceAlgebraicRealizationGenerator.fubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.fubini source target)

end AnalyticMotives
end LFunctions
end Boundary
