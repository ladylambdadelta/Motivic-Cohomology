import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.Generators.Owner

/-!
# Algebraic soundness of rewrite generators

This file owns the algebraic soundness theorems for one-step computadic rewrite
generators.

Each theorem here records the concrete representable-presheaf interpretation
currently available for one synthetic generator: the map's Yoneda preimage is
the corresponding typed trace hom.  Downstream comparison files can identify these
trace homs with finite-correspondence, localization, Gysin, base-change,
projection-formula, or trace operations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Algebraic Stokes soundness is represented by the Stokes trace hom. -/
theorem TraceAlgebraicSoundness.stokesGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.stokesMap source target) =
      (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAlgebraicRealizationGenerator.stokesMap_preimage
    source
    target

/-- Algebraic residue soundness is represented by the residue trace hom. -/
theorem TraceAlgebraicSoundness.residueGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.residueMap source target) =
      (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAlgebraicRealizationGenerator.residueMap_preimage
    source
    target

/-- Algebraic channel soundness is represented by the channel trace hom. -/
theorem TraceAlgebraicSoundness.channelGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.channelMap source target) =
      (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAlgebraicRealizationGenerator.channelMap_preimage
    source
    target

/-- Algebraic refinement soundness is represented by the refinement trace hom. -/
theorem TraceAlgebraicSoundness.refinementGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.refinementMap source target) =
      (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAlgebraicRealizationGenerator.refinementMap_preimage
    source
    target

/-- Algebraic schedule soundness is represented by the schedule trace hom. -/
theorem TraceAlgebraicSoundness.scheduleGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.scheduleMap source target) =
      (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAlgebraicRealizationGenerator.scheduleMap_preimage
    source
    target

/-- Algebraic weight-drop soundness is represented by the weight-drop trace hom. -/
theorem TraceAlgebraicSoundness.weightDropGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.weightDropMap source target) =
      (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAlgebraicRealizationGenerator.weightDropMap_preimage
    source
    target

/-- Algebraic Fubini soundness is represented by the Fubini trace hom. -/
theorem TraceAlgebraicSoundness.fubiniGenerator_preimage
    (source target : QTraceExpression) :
    TraceCorQPresheaf.representablePreimage
        (TraceAlgebraicRealizationGenerator.fubiniMap source target) =
      (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAlgebraicRealizationGenerator.fubiniMap_preimage
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
