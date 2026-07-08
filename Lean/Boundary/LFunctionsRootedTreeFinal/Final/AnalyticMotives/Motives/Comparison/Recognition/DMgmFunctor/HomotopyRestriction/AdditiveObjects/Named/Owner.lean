import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmFunctor.HomotopyRestriction.AdditiveObjects.Owner

/-!
# Named additive-object restriction formulas

This file specializes the additive finite-family restriction formula to the
seven named analytic rewrite generators.
-/

universe u

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- Additive finite-family restriction formula for Stokes. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_stokesMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.stokes source target)) =
      (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.stokes source target)

/-- Additive finite-family restriction formula for residue. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_residueMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.residue source target)) =
      (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.residue source target)

/-- Additive finite-family restriction formula for channel. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_channelMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.channel source target)) =
      (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.channel source target)

/-- Additive finite-family restriction formula for refinement. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_refinementMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.refinement source target)) =
      (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.refinement source target)

/-- Additive finite-family restriction formula for schedule. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_scheduleMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.schedule source target)) =
      (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.schedule source target)

/-- Additive finite-family restriction formula for weight-drop. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_weightDropMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.weightDrop source target)) =
      (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.weightDrop source target)

/-- Additive finite-family restriction formula for Fubini. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_fubiniMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.fubini source target)) =
      (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    homotopyFunctor
    (TraceRewriteGenerator.fubini source target)

end AnalyticMotives
end LFunctions
end Boundary
