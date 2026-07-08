import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.HomotopyRestriction.AdditiveObjects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.HomotopyRestriction.AdditiveObjects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.Owner

/-!
# Stable additive-object restriction of full recognition functors from geometric data

This file restricts the full Boundary-DMgm recognition functor induced from
geometric data to additive finite trace families.
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

/-- The full recognition-from-geometric functor restricted to stable additive
finite trace families. -/
def TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticAdditiveCategoryObject ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor ⋙
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition)
      twistData
      homotopyFunctor
      inverts

/-- The full recognition-from-geometric additive restriction is stable additive
source followed by the full recognition functor induced from geometric data. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_eq_comp
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts =
      TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor ⋙
        TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
          (composition := composition)
          twistData
          homotopyFunctor
          inverts :=
  rfl

/-- Object formula for the full recognition-from-geometric additive
restriction. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_obj
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (object : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).obj object =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).obj
        (TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.obj
          object) :=
  rfl

/-- Map formula for the full recognition-from-geometric additive restriction. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_map
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.map
          hom) :=
  rfl

/-- The descended stable full-from-geometric additive restriction sends a
rewrite generator's additive stage through the stable additive source and then
through the descended full-from-geometric recognition functor. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor_rewriteGeneratorMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (generator : TraceRewriteGenerator) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          generator) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).map
        (TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            generator)) :=
  rfl

/-- The descended stable full-from-geometric additive restriction compares
objectwise with the postcomposed homotopy-level additive restriction. -/
def TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (object : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).obj object ≅
      (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).obj object :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceAnalyticAdditiveHomotopyCategory.objectOf
      ((CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
        (0 : ℤ)).obj object))

/-- Naturality of the additive-object comparison isomorphism for the
full-from-geometric stable restriction. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map hom ≫
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        target).hom =
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        source).hom ≫
        (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map hom :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    (homotopyFunctor ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition) twistData homotopyFunctor inverts)
    (TraceAnalyticAdditiveHomotopyCategory.mapOf
      ((CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
        (0 : ℤ)).map hom))

/-- Naturality of the additive-object comparison isomorphism on a rewrite
generator's additive stage. -/
theorem TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_rewriteGenerator_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (generator : TraceRewriteGenerator) :
    (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          generator) ≫
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          generator.targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
          generator.sourceObject)).hom ≫
        (TraceAnalyticMotiveRecognition.fullFromGeometricAdditiveObjectRestrictionFunctor
          (composition := composition)
          twistData
          homotopyFunctor).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
            generator) :=
  TraceAnalyticMotiveRecognition.descendedFullFromGeometricAdditiveObjectRestrictionObjectIso_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap generator)

end AnalyticMotives
end LFunctions
end Boundary
