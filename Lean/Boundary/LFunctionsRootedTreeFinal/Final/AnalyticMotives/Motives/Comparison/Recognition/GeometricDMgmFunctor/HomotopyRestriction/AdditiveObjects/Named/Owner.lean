import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.HomotopyRestriction.AdditiveObjects.Owner

/-!
# Named geometric additive-object restriction formulas

This file specializes the geometric additive finite-family restriction formula
to the seven named analytic rewrite generators.
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

variable (twistData :
  TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
    (composition := composition))

/-- Geometric additive finite-family restriction formula for Stokes. -/
theorem TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_stokesMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.stokes source target)) =
      (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.stokes source target).traceHom :=
  TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.stokes source target)

/-- Geometric additive finite-family restriction formula for residue. -/
theorem TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_residueMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.residue source target)) =
      (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.residue source target).traceHom :=
  TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.residue source target)

/-- Geometric additive finite-family restriction formula for channel. -/
theorem TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_channelMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.channel source target)) =
      (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.channel source target).traceHom :=
  TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.channel source target)

/-- Geometric additive finite-family restriction formula for refinement. -/
theorem TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_refinementMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.refinement source target)) =
      (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.refinement source target).traceHom :=
  TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.refinement source target)

/-- Geometric additive finite-family restriction formula for schedule. -/
theorem TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_scheduleMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.schedule source target)) =
      (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.schedule source target).traceHom :=
  TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.schedule source target)

/-- Geometric additive finite-family restriction formula for weight-drop. -/
theorem TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_weightDropMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.weightDrop source target)) =
      (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.weightDrop source target).traceHom :=
  TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.weightDrop source target)

/-- Geometric additive finite-family restriction formula for Fubini. -/
theorem TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_fubiniMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          (TraceRewriteGenerator.fubini source target)) =
      (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.fubini source target).traceHom :=
  TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.fubini source target)

end AnalyticMotives
end LFunctions
end Boundary
