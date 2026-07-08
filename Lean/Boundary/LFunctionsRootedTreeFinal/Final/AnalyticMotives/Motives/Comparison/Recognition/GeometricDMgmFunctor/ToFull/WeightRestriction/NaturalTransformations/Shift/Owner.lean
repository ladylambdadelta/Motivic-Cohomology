import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Components.Weights.Bounded.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Naturality.Weights.Bounded.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.WeightRestriction.NaturalTransformations.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.WeightRestriction.Shift.Owner

/-!
# Shifted bounded natural transformations for full recognition functors

This file specializes descended Boundary-DMgm natural transformations to the
shifted bounded-weight restriction of full recognition functors induced from
geometric recognition data.
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

/-- Component formula for a full-from-geometric descended natural
transformation at a shifted stable bounded analytic object. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans_app_shiftedBoundedObject
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation :
      first ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData ⟶
      second ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          degree) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricShiftedBoundedObjectIso
        (composition := composition)
        twistData
        first
        firstInverts
        complex
        degree).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
          complex
          degree) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricShiftedBoundedObjectIso
        (composition := composition)
        twistData
        second
        secondInverts
        complex
        degree).inv :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_shiftedBoundedObject
    (composition := composition)
    (first ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (second ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      first
      firstInverts)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      second
      secondInverts)
    transformation
    complex
    degree

/-- Naturality of a full-from-geometric descended natural transformation on a
shifted stable bounded analytic chain map. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans_shiftedBoundedMap_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation :
      first ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData ⟶
      second ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          source
          degree) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
            hom
            degree) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedMap
            hom
            degree) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            target
            degree) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_shiftedBoundedMap_naturality
    (composition := composition)
    (first ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (second ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      first
      firstInverts)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      second
      secondInverts)
    transformation
    hom
    degree

end AnalyticMotives
end LFunctions
end Boundary
