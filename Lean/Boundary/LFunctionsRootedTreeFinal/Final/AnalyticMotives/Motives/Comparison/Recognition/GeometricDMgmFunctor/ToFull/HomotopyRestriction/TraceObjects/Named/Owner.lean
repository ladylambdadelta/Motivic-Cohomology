import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.HomotopyRestriction.TraceObjects.Owner

/-!
# Named full-from-geometric trace-object restriction formulas

This file specializes the full-from-geometric trace-object restriction formula
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

/-- Full-from-geometric trace-object restriction formula for Stokes. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_stokesMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.stokes source target).traceHom =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceRewriteGenerator.stokes source target).traceHom) :=
  TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.stokes source target)

/-- Full-from-geometric trace-object restriction formula for residue. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_residueMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.residue source target).traceHom =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceRewriteGenerator.residue source target).traceHom) :=
  TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.residue source target)

/-- Full-from-geometric trace-object restriction formula for channel. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_channelMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.channel source target).traceHom =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceRewriteGenerator.channel source target).traceHom) :=
  TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.channel source target)

/-- Full-from-geometric trace-object restriction formula for refinement. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_refinementMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.refinement source target).traceHom =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceRewriteGenerator.refinement source target).traceHom) :=
  TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.refinement source target)

/-- Full-from-geometric trace-object restriction formula for schedule. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_scheduleMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.schedule source target).traceHom =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceRewriteGenerator.schedule source target).traceHom) :=
  TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.schedule source target)

/-- Full-from-geometric trace-object restriction formula for weight-drop. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_weightDropMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.weightDrop source target).traceHom =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceRewriteGenerator.weightDrop source target).traceHom) :=
  TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.weightDrop source target)

/-- Full-from-geometric trace-object restriction formula for Fubini. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_fubiniMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (source target : QTraceExpression) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceRewriteGenerator.fubini source target).traceHom =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceRewriteGenerator.fubini source target).traceHom) :=
  TraceAnalyticMotiveRecognition.fullFromGeometricTraceObjectRestrictionFunctor_rewriteGeneratorMap
    (composition := composition)
    twistData
    homotopyFunctor
    (TraceRewriteGenerator.fubini source target)

end AnalyticMotives
end LFunctions
end Boundary
