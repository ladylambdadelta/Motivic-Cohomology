import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.HomotopyRestriction.TraceObjects.Owner

/-!
# Additive-object restriction of geometric homotopy-level recognition functors

This file records the concrete finite-family restriction for homotopy-level
functors landing in the geometric Boundary-DMgm target.
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

/-- The additive finite-family restriction of a geometric homotopy-level
recognition functor. -/
def TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData) :
    TraceAnalyticAdditiveCategoryObject ⥤
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData :=
  CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject (0 : ℤ) ⋙
    TraceAnalyticAdditiveHomotopyCategory.quotientFunctor ⋙
      homotopyFunctor

/-- Object formula for the geometric additive finite-family restriction. -/
theorem TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_obj
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (object : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).obj object =
      homotopyFunctor.obj
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          ((CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
            (0 : ℤ)).obj object)) :=
  rfl

/-- Map formula for the geometric additive finite-family restriction. -/
theorem TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_map
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map hom =
      homotopyFunctor.map
        (TraceAnalyticAdditiveHomotopyCategory.mapOf
          ((CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
            (0 : ℤ)).map hom)) :=
  rfl

/-- On singleton additive objects, the geometric additive finite-family
restriction recovers the geometric trace-object restriction. -/
theorem TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_obj_singleton
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (object : TraceCorQObject) :
    (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).obj
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject object) =
      (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).obj object :=
  rfl

/-- On singleton trace matrices, the geometric additive finite-family
restriction recovers the geometric trace-object restriction. -/
theorem TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_map_singleton
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveMap hom) =
      (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map hom :=
  rfl

/-- The geometric additive finite-family restriction sends a rewrite
generator's additive stage to the same target map as its geometric trace-object
restriction. -/
theorem TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (generator : TraceRewriteGenerator) :
    (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          generator) =
      (TraceAnalyticMotiveRecognition.geometricTraceObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).map generator.traceHom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
