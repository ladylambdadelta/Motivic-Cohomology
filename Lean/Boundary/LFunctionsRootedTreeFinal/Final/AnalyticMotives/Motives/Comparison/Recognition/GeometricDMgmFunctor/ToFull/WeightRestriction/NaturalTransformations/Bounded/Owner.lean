import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Components.Weights.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Naturality.Weights.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.WeightRestriction.Bounded.Owner

/-!
# Bounded natural transformations for full recognition functors

This file specializes descended Boundary-DMgm natural transformations to the
bounded-weight restriction of full recognition functors induced from geometric
recognition data.
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

/-- Descended natural transformation between full recognition functors induced
from geometric recognition data, expressed after postcomposition with the
geometric-to-full target functor. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
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
          (composition := composition) twistData) :
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition)
      twistData
      first
      firstInverts ⟶
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition)
      twistData
      second
      secondInverts :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
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

/-- The full-from-geometric descended natural transformation is the ordinary
Boundary-DMgm descended natural transformation for the postcomposed homotopy
functors. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans_eq_descended
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
          (composition := composition) twistData) :
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation =
      TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans
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
        transformation :=
  rfl

/-- Component formula for a full-from-geometric descended natural
transformation at a stable bounded analytic object. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans_app_boundedObject
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
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          complex) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricBoundedObjectIso
        (composition := composition)
        twistData
        first
        firstInverts
        complex).hom ≫
      transformation.app
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricBoundedObjectIso
        (composition := composition)
        twistData
        second
        secondInverts
        complex).inv :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_boundedObject
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

/-- Naturality of a full-from-geometric descended natural transformation on a
stable bounded analytic chain map. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans_boundedMap_naturality
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
        target) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          source) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedMap hom) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
            target) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_boundedMap_naturality
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

end AnalyticMotives
end LFunctions
end Boundary
