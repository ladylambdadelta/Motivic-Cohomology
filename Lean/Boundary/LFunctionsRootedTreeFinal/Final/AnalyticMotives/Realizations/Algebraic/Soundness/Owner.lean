import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Soundness.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Soundness.Paths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Soundness.Coherence.Owner

/-!
# Algebraic soundness

This directory owns the proof that the algebraic realization faithfully
interprets the synthetic trace computad.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Root algebraic soundness wrapper for Stokes generators. -/
theorem TraceAlgebraicSoundness.stokes_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAlgebraicSoundness.stokesGenerator_preimage
    source
    target

/-- Root algebraic soundness wrapper for residue generators. -/
theorem TraceAlgebraicSoundness.residue_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAlgebraicSoundness.residueGenerator_preimage
    source
    target

/-- Root algebraic soundness wrapper for channel generators. -/
theorem TraceAlgebraicSoundness.channel_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAlgebraicSoundness.channelGenerator_preimage
    source
    target

/-- Root algebraic soundness wrapper for refinement generators. -/
theorem TraceAlgebraicSoundness.refinement_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAlgebraicSoundness.refinementGenerator_preimage
    source
    target

/-- Root algebraic soundness wrapper for schedule generators. -/
theorem TraceAlgebraicSoundness.schedule_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAlgebraicSoundness.scheduleGenerator_preimage
    source
    target

/-- Root algebraic soundness wrapper for weight-drop generators. -/
theorem TraceAlgebraicSoundness.weightDrop_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAlgebraicSoundness.weightDropGenerator_preimage
    source
    target

/-- Root algebraic soundness wrapper for Fubini generators. -/
theorem TraceAlgebraicSoundness.fubini_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAlgebraicSoundness.fubiniGenerator_preimage
    source
    target

/-- Root algebraic soundness wrapper for finite path step counts. -/
theorem TraceAlgebraicSoundness.path_comp_steps
    (first second : TraceRewritePath) :
    (TraceRewritePath.comp first second).stepCount =
      first.stepCount + second.stepCount :=
  TraceAlgebraicSoundness.path_comp_stepCount
    first
    second

/-- Root algebraic soundness wrapper for residue-channel coherence kind. -/
theorem TraceAlgebraicSoundness.residueChannel_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.residueChannel source target).kind =
      TraceCoherenceKind.residueChannel :=
  TraceAlgebraicSoundness.residueChannelCoherence_kind
    source
    target

/-- Root algebraic soundness wrapper for associativity coherence kind. -/
theorem TraceAlgebraicSoundness.associativity_kind
    (source target : TraceRewritePath) :
    (TraceCoherenceCell.associativity source target).kind =
      TraceCoherenceKind.associativity :=
  TraceAlgebraicSoundness.associativityCoherence_kind
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
