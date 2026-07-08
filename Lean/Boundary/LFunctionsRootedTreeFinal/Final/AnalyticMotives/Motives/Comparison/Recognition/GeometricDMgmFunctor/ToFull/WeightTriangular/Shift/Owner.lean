import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.WeightRestriction.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.WeightTriangular.Bounded.Owner

/-!
# Shifted bounded weight-triangular surface for full recognition functors

This file records the shifted bounded-representative part of the
weight-triangular comparison surface for full recognition functors induced from
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

/-- The full-from-geometric recognition functor sends a shifted stable bounded
analytic representative to the corresponding full Boundary-DMgm image of its
shifted bounded homotopy representative. -/
def TraceAnalyticMotiveRecognition.weightTriangularShiftedBoundedObjectIso
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
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricShiftedBoundedObjectIso
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    complex
    degree

/-- The shifted bounded weight-triangular object isomorphism is the existing
shifted bounded descent comparison isomorphism. -/
theorem TraceAnalyticMotiveRecognition.weightTriangularShiftedBoundedObjectIso_eq
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
    TraceAnalyticMotiveRecognition.weightTriangularShiftedBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        complex
        degree =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricShiftedBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        complex
        degree :=
  rfl

/-- Shifted bounded maps satisfy the weight-triangular naturality square for
the full-from-geometric recognition functor. -/
theorem TraceAnalyticMotiveRecognition.weightTriangular_shiftedBoundedMap_naturality
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
      (TraceAnalyticMotiveRecognition.weightTriangularShiftedBoundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        target
        degree).hom =
      (TraceAnalyticMotiveRecognition.weightTriangularShiftedBoundedObjectIso
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
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_shiftedBoundedMap_naturality
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    hom
    degree

end AnalyticMotives
end LFunctions
end Boundary
