import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.HomotopyRestriction.AdditiveObjects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.HomotopyRestriction.TraceObjects.Owner

/-!
# Additive-object restriction of full recognition functors from geometric data

This file records the homotopy-level additive finite-family restriction
obtained from geometric recognition data by postcomposing with the
geometric-to-full Boundary-DMgm target functor.
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

/-- The homotopy-level additive restriction postcomposed with the
geometric-to-full target functor. -/
def TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData) :
    TraceAnalyticAdditiveCategoryObject ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
    (composition := composition)
    twistData
    homotopyFunctor ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData

/-- The full-from-geometric homotopy-level additive restriction is the
geometric additive restriction followed by the geometric-to-full target
functor. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor_eq_comp
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData) :
    TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor =
      TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData :=
  rfl

/-- Object formula for the full-from-geometric homotopy-level additive
restriction. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor_obj
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (object : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).obj object =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj
        ((TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).obj object) :=
  rfl

/-- Map formula for the full-from-geometric homotopy-level additive
restriction. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor_map
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map hom =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map
        ((TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map hom) :=
  rfl

/-- On singleton additive objects, the full-from-geometric homotopy-level
additive restriction is the geometric trace-object restriction followed by the
geometric-to-full target functor. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor_obj_singleton
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (object : TraceCorQObject) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).obj
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject object) =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).obj object) :=
  rfl

/-- On singleton trace matrices, the full-from-geometric homotopy-level
additive restriction is the geometric trace-object restriction followed by the
geometric-to-full target functor. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor_map_singleton
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveMap hom) =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map hom) :=
  rfl

/-- The full-from-geometric homotopy-level additive restriction sends a rewrite
generator's additive stage to the geometric trace-object restriction map
followed by the geometric-to-full target functor. -/
theorem TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (generator : TraceRewriteGenerator) :
    (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          generator) =
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map
        ((TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map generator.traceHom) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
