import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Weights.Bounded.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.WeightRestriction.Bounded.Owner

/-!
# Shifted bounded-weight restriction of full recognition functors

This file specializes the full Boundary-DMgm recognition functor induced from
geometric recognition data to stable shifted bounded analytic complexes and
shifted bounded chain maps.
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

/-- Object comparison isomorphism for the full-from-geometric recognition
functor on a stable shifted bounded analytic complex. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricShiftedBoundedObjectIso
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
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          complex
          degree) ≅
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj
        (homotopyFunctor.obj
          (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
            complex
            degree)) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
    (composition := composition)
    (homotopyFunctor ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      homotopyFunctor
      inverts)
    complex
    degree

/-- The shifted bounded object comparison isomorphism is the Boundary-DMgm
shifted bounded descent projection for the postcomposed homotopy functor. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricShiftedBoundedObjectIso_eq_descended
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
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricShiftedBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        complex
        degree =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorShiftedBoundedObjectIso
        (composition := composition)
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData)
        (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
          (composition := composition)
          twistData
          homotopyFunctor
          inverts)
        complex
        degree :=
  rfl

/-- Naturality of the full-from-geometric recognition functor on a shifted
stable map represented by a bounded analytic chain map. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_shiftedBoundedMap_naturality
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
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricShiftedBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        target
        degree).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricShiftedBoundedObjectIso
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
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_shiftedBoundedMap_naturality
    (composition := composition)
    (homotopyFunctor ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition)
      twistData
      homotopyFunctor
      inverts)
    hom
    degree

end AnalyticMotives
end LFunctions
end Boundary
