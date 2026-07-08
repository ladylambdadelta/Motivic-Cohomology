import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.WeightTriangular.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Representatives.Shift.Owner

/-!
# Weight-triangular comparison for analytic heart representatives

This file specializes the shifted bounded weight-triangular object comparison
to exact-degree heart representatives and translated exact-degree heart
representatives through the concrete heart inclusion.
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

/-- The full-from-geometric recognition functor sends an exact-degree analytic
heart representative, after forgetting to the stable comparison source, to the
corresponding full Boundary-DMgm image of its shifted bounded homotopy
representative. -/
def TraceAnalyticMotiveRecognition.weightTriangularHeartRepresentativeObjectIso
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).obj
        ((TraceAnalyticMotivicTStructure.Heart.inclusion degree).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelf
            complex
            degree)) ≅
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj
        (homotopyFunctor.obj
          (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
            complex
            degree)) :=
  TraceAnalyticMotiveRecognition.weightTriangularShiftedBoundedObjectIso
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    complex
    degree

/-- The exact-degree heart-representative comparison isomorphism is the shifted
bounded weight-triangular object comparison isomorphism. -/
theorem TraceAnalyticMotiveRecognition.weightTriangularHeartRepresentativeObjectIso_eq_shiftedBounded
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotiveRecognition.weightTriangularHeartRepresentativeObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        complex
        degree =
      TraceAnalyticMotiveRecognition.weightTriangularShiftedBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        complex
        degree :=
  rfl

/-- Bounded chain maps between exact-degree heart representatives satisfy the
shifted bounded weight-triangular naturality square after forgetting the heart
objects to the stable comparison source. -/
theorem TraceAnalyticMotiveRecognition.weightTriangular_heartRepresentativeMap_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
          hom
          degree) ≫
      (TraceAnalyticMotiveRecognition.weightTriangularHeartRepresentativeObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        target
        degree).hom =
      (TraceAnalyticMotiveRecognition.weightTriangularHeartRepresentativeObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        source
        degree).hom ≫
        (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData).map
          (homotopyFunctor.map
            (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
              hom
              degree)) :=
  TraceAnalyticMotiveRecognition.weightTriangular_shiftedBoundedMap_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    hom
    degree

/-- The full-from-geometric recognition functor sends a translated exact-degree
analytic heart representative, after forgetting to the stable comparison
source, to the corresponding full Boundary-DMgm image of its translated shifted
bounded homotopy representative. -/
def TraceAnalyticMotiveRecognition.weightTriangularTranslatedHeartRepresentativeObjectIso
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).obj
        ((TraceAnalyticMotivicTStructure.Heart.inclusion
          (degree + shift)).obj
          (TraceAnalyticMotivicTStructure.Heart.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)) ≅
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj
        (homotopyFunctor.obj
          (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
            complex
            (degree + shift))) :=
  TraceAnalyticMotiveRecognition.weightTriangularShiftedBoundedObjectIso
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    complex
    (degree + shift)

/-- The translated heart-representative comparison isomorphism is the shifted
bounded weight-triangular object comparison isomorphism at the translated
degree. -/
theorem TraceAnalyticMotiveRecognition.weightTriangularTranslatedHeartRepresentativeObjectIso_eq_shiftedBounded
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotiveRecognition.weightTriangularTranslatedHeartRepresentativeObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        shift
        complex
        degree =
      TraceAnalyticMotiveRecognition.weightTriangularShiftedBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        complex
        (degree + shift) :=
  rfl

/-- Bounded chain maps between translated exact-degree heart representatives
satisfy the shifted bounded weight-triangular naturality square at the
translated degree after forgetting the heart objects to the stable comparison
source. -/
theorem TraceAnalyticMotiveRecognition.weightTriangular_translatedHeartRepresentativeMap_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (shift : ℤ)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
          hom
          (degree + shift)) ≫
      (TraceAnalyticMotiveRecognition.weightTriangularTranslatedHeartRepresentativeObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        shift
        target
        degree).hom =
      (TraceAnalyticMotiveRecognition.weightTriangularTranslatedHeartRepresentativeObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        shift
        source
        degree).hom ≫
        (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData).map
          (homotopyFunctor.map
            (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyMap
              hom
              (degree + shift))) :=
  TraceAnalyticMotiveRecognition.weightTriangular_shiftedBoundedMap_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    hom
    (degree + shift)

end AnalyticMotives
end LFunctions
end Boundary
