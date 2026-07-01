import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.RewriteMaps.ByKind.Owner

/-!
# Analytic realization generator maps

This file owns concrete representable-presheaf maps used by the analytic
realization layer before any comparison or localization theorem is stated.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A residue-extraction map used by the analytic trace-value realization. -/
def TraceAnalyticRealizationGenerator.residueMap
    (source target : QTraceExpression) :
    TraceCorQPresheafHom
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.residue source target).sourceObject)
      (TraceCorQPresheaf.representable
        (TraceRewriteGenerator.residue source target).targetObject) :=
  TraceRewriteGenerator.residueRepresentableMap source target

/-- The analytic realization residue map is the by-kind residue representable map. -/
theorem TraceAnalyticRealizationGenerator.residueMap_eq
    (source target : QTraceExpression) :
    TraceAnalyticRealizationGenerator.residueMap source target =
      TraceRewriteGenerator.residueRepresentableMap source target :=
  rfl

/-- The trace preimage of an analytic realization residue map is the residue trace hom. -/
theorem TraceAnalyticRealizationGenerator.residueMap_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAnalyticRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceRewriteGenerator.representableMap_preimage
    (TraceRewriteGenerator.residue source target)

end AnalyticMotives
end LFunctions
end Boundary
