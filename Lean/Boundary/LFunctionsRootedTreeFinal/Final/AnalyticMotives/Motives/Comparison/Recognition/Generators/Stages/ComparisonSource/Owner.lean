import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.Generators.Stages.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Functoriality.Owner

/-!
# Comparison-source formulas for recognition generator stages

The staged stable map of a concrete rewrite generator lives in the analytic
comparison source.  This file records its formula through
`TraceAnalyticDMgmComparisonSource.mapOf`, so recognition proofs can use the
comparison-source API directly.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The stable source map of a rewrite generator is the comparison-source
quotient image of its homotopy source map. -/
theorem TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap_eq_comparisonSource_mapOf
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap generator =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          generator) :=
  Eq.trans
    (TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap_eq_sourceMapOf
      generator)
    (TraceAnalyticMotiveComparison.sourceMapOf_eq_source
      (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
        generator))

end AnalyticMotives
end LFunctions
end Boundary
