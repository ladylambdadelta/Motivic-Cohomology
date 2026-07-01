import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.RewriteMaps.ByKind.Owner

/-!
# Interval-homotopy generator maps

This file owns the concrete representable-presheaf maps that generate analytic
interval homotopy before localization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Stokes deformation map to be imposed by interval homotopy. -/
def TraceIntervalHomotopyGenerator.stokesMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.stokes source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.stokes source target).targetObject) :=
  TraceRewriteGenerator.stokesRepresentableMap source target

/-- A Fubini interchange map to be imposed by interval homotopy. -/
def TraceIntervalHomotopyGenerator.fubiniMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.fubini source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.fubini source target).targetObject) :=
  TraceRewriteGenerator.fubiniRepresentableMap source target

/-- The interval-homotopy Stokes map is the by-kind Stokes representable map. -/
theorem TraceIntervalHomotopyGenerator.stokesMap_eq
    (source target : QTraceExpression) :
    TraceIntervalHomotopyGenerator.stokesMap source target =
      TraceRewriteGenerator.stokesRepresentableMap source target :=
  rfl

/-- The interval-homotopy Fubini map is the by-kind Fubini representable map. -/
theorem TraceIntervalHomotopyGenerator.fubiniMap_eq
    (source target : QTraceExpression) :
    TraceIntervalHomotopyGenerator.fubiniMap source target =
      TraceRewriteGenerator.fubiniRepresentableMap source target :=
  rfl

/-- The trace preimage of an interval Stokes map is the Stokes trace hom. -/
theorem TraceIntervalHomotopyGenerator.stokesMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceIntervalHomotopyGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.stokes source target)

/-- The trace preimage of an interval Fubini map is the Fubini trace hom. -/
theorem TraceIntervalHomotopyGenerator.fubiniMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceIntervalHomotopyGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.fubini source target)

end AnalyticMotives
end LFunctions
end Boundary
