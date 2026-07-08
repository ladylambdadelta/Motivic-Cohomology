import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Soundness.Paths.Owner

/-!
# Top-root algebraic path soundness

This file exposes concrete finite-path data preserved by the algebraic
realization at the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Algebraic path interpretation reads the same source expression as the path syntax. -/
theorem AnalyticMotivesRoot.algebraicSoundness_path_source
    (path : TraceRewritePath) :
    path.source =
      TraceRewritePath.source path :=
  TraceAlgebraicSoundness.path_source
    path

/-- Algebraic path interpretation reads the same target expression as the path syntax. -/
theorem AnalyticMotivesRoot.algebraicSoundness_path_target
    (path : TraceRewritePath) :
    path.target =
      TraceRewritePath.target path :=
  TraceAlgebraicSoundness.path_target
    path

/-- Algebraic path interpretation keeps the finite rewrite-step count. -/
theorem AnalyticMotivesRoot.algebraicSoundness_path_stepCount
    (path : TraceRewritePath) :
    path.stepCount =
      TraceRewritePath.stepCount path :=
  TraceAlgebraicSoundness.path_stepCount
    path

/-- Algebraic interpretation of a one-step generator path has the generator source. -/
theorem AnalyticMotivesRoot.algebraicSoundness_generatorPath_source
    (generator : TraceRewriteGenerator) :
    (TraceRewritePath.ofGenerator generator).source =
      generator.source :=
  TraceAlgebraicSoundness.generatorPath_source
    generator

/-- Algebraic interpretation of a one-step generator path has the generator target. -/
theorem AnalyticMotivesRoot.algebraicSoundness_generatorPath_target
    (generator : TraceRewriteGenerator) :
    (TraceRewritePath.ofGenerator generator).target =
      generator.target :=
  TraceAlgebraicSoundness.generatorPath_target
    generator

/-- Algebraic interpretation of path concatenation adds step counts. -/
theorem AnalyticMotivesRoot.algebraicSoundness_path_comp_stepCount
    (first second : TraceRewritePath) :
    (TraceRewritePath.comp first second).stepCount =
      first.stepCount + second.stepCount :=
  TraceAlgebraicSoundness.path_comp_stepCount
    first
    second

end AnalyticMotives
end LFunctions
end Boundary
