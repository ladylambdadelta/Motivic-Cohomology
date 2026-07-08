import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.Generators.Stages.Owner

/-!
# Named recognition generator stages

This file connects the seven named recognition stable-source maps to the
generic stage decomposition for a concrete rewrite generator.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The named Stokes stable-source map is the generic stable map of the Stokes
rewrite generator. -/
theorem TraceAnalyticMotiveRecognition.stokesStableSourceMap_eq_rewriteGeneratorStableMap
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.stokesStableSourceMap source target =
      TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap
        (TraceRewriteGenerator.stokes source target) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.stokesStableSourceMap_eq_sourceTraceFunctor_map
      source
      target)
    (TraceAnalyticMotiveComparison.sourceTraceFunctor_map
      (TraceRewriteGenerator.stokes source target).traceHom)

/-- The named residue stable-source map is the generic stable map of the
residue rewrite generator. -/
theorem TraceAnalyticMotiveRecognition.residueStableSourceMap_eq_rewriteGeneratorStableMap
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.residueStableSourceMap source target =
      TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap
        (TraceRewriteGenerator.residue source target) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.residueStableSourceMap_eq_sourceTraceFunctor_map
      source
      target)
    (TraceAnalyticMotiveComparison.sourceTraceFunctor_map
      (TraceRewriteGenerator.residue source target).traceHom)

/-- The named channel stable-source map is the generic stable map of the
channel rewrite generator. -/
theorem TraceAnalyticMotiveRecognition.channelStableSourceMap_eq_rewriteGeneratorStableMap
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.channelStableSourceMap source target =
      TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap
        (TraceRewriteGenerator.channel source target) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.channelStableSourceMap_eq_sourceTraceFunctor_map
      source
      target)
    (TraceAnalyticMotiveComparison.sourceTraceFunctor_map
      (TraceRewriteGenerator.channel source target).traceHom)

/-- The named refinement stable-source map is the generic stable map of the
refinement rewrite generator. -/
theorem TraceAnalyticMotiveRecognition.refinementStableSourceMap_eq_rewriteGeneratorStableMap
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.refinementStableSourceMap source target =
      TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap
        (TraceRewriteGenerator.refinement source target) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.refinementStableSourceMap_eq_sourceTraceFunctor_map
      source
      target)
    (TraceAnalyticMotiveComparison.sourceTraceFunctor_map
      (TraceRewriteGenerator.refinement source target).traceHom)

/-- The named schedule stable-source map is the generic stable map of the
schedule rewrite generator. -/
theorem TraceAnalyticMotiveRecognition.scheduleStableSourceMap_eq_rewriteGeneratorStableMap
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.scheduleStableSourceMap source target =
      TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap
        (TraceRewriteGenerator.schedule source target) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.scheduleStableSourceMap_eq_sourceTraceFunctor_map
      source
      target)
    (TraceAnalyticMotiveComparison.sourceTraceFunctor_map
      (TraceRewriteGenerator.schedule source target).traceHom)

/-- The named weight-drop stable-source map is the generic stable map of the
weight-drop rewrite generator. -/
theorem TraceAnalyticMotiveRecognition.weightDropStableSourceMap_eq_rewriteGeneratorStableMap
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.weightDropStableSourceMap source target =
      TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap
        (TraceRewriteGenerator.weightDrop source target) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.weightDropStableSourceMap_eq_sourceTraceFunctor_map
      source
      target)
    (TraceAnalyticMotiveComparison.sourceTraceFunctor_map
      (TraceRewriteGenerator.weightDrop source target).traceHom)

/-- The named Fubini stable-source map is the generic stable map of the Fubini
rewrite generator. -/
theorem TraceAnalyticMotiveRecognition.fubiniStableSourceMap_eq_rewriteGeneratorStableMap
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.fubiniStableSourceMap source target =
      TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap
        (TraceRewriteGenerator.fubini source target) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.fubiniStableSourceMap_eq_sourceTraceFunctor_map
      source
      target)
    (TraceAnalyticMotiveComparison.sourceTraceFunctor_map
      (TraceRewriteGenerator.fubini source target).traceHom)

end AnalyticMotives
end LFunctions
end Boundary
