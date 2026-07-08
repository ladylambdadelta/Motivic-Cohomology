import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Soundness.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Paths.Owner

/-!
# Algebraic soundness of rewrite paths

This file owns algebraic soundness for finite computadic rewrite paths.

The current path layer records the concrete finite path data used by the
algebraic realization: sources, targets, and step counts.  Downstream comparison
files can add the stronger path-induction theorem after the corresponding
finite-correspondence equality target is available.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Algebraic path interpretation reads the same source expression as the path syntax. -/
theorem TraceAlgebraicSoundness.path_source
    (path : TraceRewritePath) :
    path.source =
      TraceRewritePath.source path :=
  rfl

/-- Algebraic path interpretation reads the same target expression as the path syntax. -/
theorem TraceAlgebraicSoundness.path_target
    (path : TraceRewritePath) :
    path.target =
      TraceRewritePath.target path :=
  rfl

/-- Algebraic path interpretation keeps the finite rewrite-step count. -/
theorem TraceAlgebraicSoundness.path_stepCount
    (path : TraceRewritePath) :
    path.stepCount =
      TraceRewritePath.stepCount path :=
  rfl

/-- Algebraic interpretation of a one-step generator path has the generator source. -/
theorem TraceAlgebraicSoundness.generatorPath_source
    (generator : TraceRewriteGenerator) :
    (TraceRewritePath.ofGenerator generator).source =
      generator.source :=
  TraceRewritePath.ofGenerator_source
    generator

/-- Algebraic interpretation of a one-step generator path has the generator target. -/
theorem TraceAlgebraicSoundness.generatorPath_target
    (generator : TraceRewriteGenerator) :
    (TraceRewritePath.ofGenerator generator).target =
      generator.target :=
  TraceRewritePath.ofGenerator_target
    generator

/-- Algebraic interpretation of path concatenation adds step counts. -/
theorem TraceAlgebraicSoundness.path_comp_stepCount
    (first second : TraceRewritePath) :
    (TraceRewritePath.comp first second).stepCount =
      first.stepCount + second.stepCount :=
  TraceRewritePath.comp_stepCount
    first
    second

end AnalyticMotives
end LFunctions
end Boundary
