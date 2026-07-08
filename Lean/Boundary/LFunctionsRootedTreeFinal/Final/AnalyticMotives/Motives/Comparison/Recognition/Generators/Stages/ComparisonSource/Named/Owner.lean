import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.Generators.Stages.Named.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.Generators.Stages.ComparisonSource.Owner

/-!
# Named comparison-source formulas for recognition generator stages

This file specializes the comparison-source represented stable-map formula to
the seven named analytic rewrite generators.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The named Stokes stable-source map is the comparison-source quotient image
of the Stokes homotopy source map. -/
theorem TraceAnalyticMotiveRecognition.stokesStableSourceMap_eq_comparisonSource_mapOf
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.stokesStableSourceMap source target =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.stokes source target)) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.stokesStableSourceMap_eq_rewriteGeneratorStableMap
      source
      target)
    (TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap_eq_comparisonSource_mapOf
      (TraceRewriteGenerator.stokes source target))

/-- The named residue stable-source map is the comparison-source quotient
image of the residue homotopy source map. -/
theorem TraceAnalyticMotiveRecognition.residueStableSourceMap_eq_comparisonSource_mapOf
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.residueStableSourceMap source target =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.residue source target)) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.residueStableSourceMap_eq_rewriteGeneratorStableMap
      source
      target)
    (TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap_eq_comparisonSource_mapOf
      (TraceRewriteGenerator.residue source target))

/-- The named channel stable-source map is the comparison-source quotient
image of the channel homotopy source map. -/
theorem TraceAnalyticMotiveRecognition.channelStableSourceMap_eq_comparisonSource_mapOf
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.channelStableSourceMap source target =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.channel source target)) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.channelStableSourceMap_eq_rewriteGeneratorStableMap
      source
      target)
    (TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap_eq_comparisonSource_mapOf
      (TraceRewriteGenerator.channel source target))

/-- The named refinement stable-source map is the comparison-source quotient
image of the refinement homotopy source map. -/
theorem TraceAnalyticMotiveRecognition.refinementStableSourceMap_eq_comparisonSource_mapOf
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.refinementStableSourceMap source target =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.refinement source target)) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.refinementStableSourceMap_eq_rewriteGeneratorStableMap
      source
      target)
    (TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap_eq_comparisonSource_mapOf
      (TraceRewriteGenerator.refinement source target))

/-- The named schedule stable-source map is the comparison-source quotient
image of the schedule homotopy source map. -/
theorem TraceAnalyticMotiveRecognition.scheduleStableSourceMap_eq_comparisonSource_mapOf
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.scheduleStableSourceMap source target =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.schedule source target)) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.scheduleStableSourceMap_eq_rewriteGeneratorStableMap
      source
      target)
    (TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap_eq_comparisonSource_mapOf
      (TraceRewriteGenerator.schedule source target))

/-- The named weight-drop stable-source map is the comparison-source quotient
image of the weight-drop homotopy source map. -/
theorem TraceAnalyticMotiveRecognition.weightDropStableSourceMap_eq_comparisonSource_mapOf
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.weightDropStableSourceMap source target =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.weightDrop source target)) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.weightDropStableSourceMap_eq_rewriteGeneratorStableMap
      source
      target)
    (TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap_eq_comparisonSource_mapOf
      (TraceRewriteGenerator.weightDrop source target))

/-- The named Fubini stable-source map is the comparison-source quotient image
of the Fubini homotopy source map. -/
theorem TraceAnalyticMotiveRecognition.fubiniStableSourceMap_eq_comparisonSource_mapOf
    (source target : QTraceExpression) :
    TraceAnalyticMotiveRecognition.fubiniStableSourceMap source target =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          (TraceRewriteGenerator.fubini source target)) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.fubiniStableSourceMap_eq_rewriteGeneratorStableMap
      source
      target)
    (TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap_eq_comparisonSource_mapOf
      (TraceRewriteGenerator.fubini source target))

end AnalyticMotives
end LFunctions
end Boundary
