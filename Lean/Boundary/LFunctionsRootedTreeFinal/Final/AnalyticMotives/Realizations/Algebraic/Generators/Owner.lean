import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.RewriteMaps.ByKind.Owner

/-!
# Algebraic realization generator maps

This file owns concrete representable-presheaf maps used by the algebraic
realization layer before any comparison theorem is stated.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A residue-extraction map used by the algebraic trace-value realization. -/
def TraceAlgebraicRealizationGenerator.residueMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.residue source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.residue source target).targetObject) :=
  TraceRewriteGenerator.residueRepresentableMap source target

/-- The algebraic realization residue map is the by-kind residue representable map. -/
theorem TraceAlgebraicRealizationGenerator.residueMap_eq
    (source target : QTraceExpression) :
    TraceAlgebraicRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  rfl

/-- The trace preimage of an algebraic realization residue map is the residue trace hom. -/
theorem TraceAlgebraicRealizationGenerator.residueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.residue source target)

end AnalyticMotives
end LFunctions
end Boundary
