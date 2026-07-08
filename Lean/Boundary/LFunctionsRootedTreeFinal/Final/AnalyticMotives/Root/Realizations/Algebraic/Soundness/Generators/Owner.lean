import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Soundness.Generators.Owner

/-!
# Top-root algebraic generator soundness

This file exposes generator-level algebraic soundness at the public
analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Algebraic Stokes soundness is represented by the Stokes trace hom. -/
theorem AnalyticMotivesRoot.algebraicSoundness_stokesGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAlgebraicSoundness.stokesGenerator_preimage
    source
    target

/-- Algebraic residue soundness is represented by the residue trace hom. -/
theorem AnalyticMotivesRoot.algebraicSoundness_residueGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAlgebraicSoundness.residueGenerator_preimage
    source
    target

/-- Algebraic channel soundness is represented by the channel trace hom. -/
theorem AnalyticMotivesRoot.algebraicSoundness_channelGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAlgebraicSoundness.channelGenerator_preimage
    source
    target

/-- Algebraic refinement soundness is represented by the refinement trace hom. -/
theorem AnalyticMotivesRoot.algebraicSoundness_refinementGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAlgebraicSoundness.refinementGenerator_preimage
    source
    target

/-- Algebraic schedule soundness is represented by the schedule trace hom. -/
theorem AnalyticMotivesRoot.algebraicSoundness_scheduleGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAlgebraicSoundness.scheduleGenerator_preimage
    source
    target

/-- Algebraic weight-drop soundness is represented by the weight-drop trace hom. -/
theorem AnalyticMotivesRoot.algebraicSoundness_weightDropGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAlgebraicSoundness.weightDropGenerator_preimage
    source
    target

/-- Algebraic Fubini soundness is represented by the Fubini trace hom. -/
theorem AnalyticMotivesRoot.algebraicSoundness_fubiniGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAlgebraicSoundness.fubiniGenerator_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
