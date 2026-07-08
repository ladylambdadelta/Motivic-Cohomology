import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.RecognitionTheorem.WeightTriangular.Heart.Representatives.Owner

/-!
# Complete heart-representative weight-triangular recognition packages

This file pairs heart-representative object comparison data with map-level
naturality equations for exact and translated analytic heart representatives.
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

/-- Complete exact heart-representative recognition package: object comparison
data together with heart-representative map weight-triangular naturality. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularHeartRepresentativeMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts).FullyFaithful)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    { objectData :
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_heartRepresentativeObjectIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      source
      degree) ×
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_heartRepresentativeObjectIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      target
      degree) //
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_heartRepresentativeMap
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom
      degree).2 } :=
  Subtype.mk
    (Prod.mk
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_heartRepresentativeObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        source
        degree)
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_heartRepresentativeObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        target
        degree))
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_heartRepresentativeMap
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom
      degree).2

/-- Complete translated heart-representative recognition package: object
comparison data together with translated heart-representative map
weight-triangular naturality. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularTranslatedHeartRepresentativeMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts).FullyFaithful)
    (shift : ℤ)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    { objectData :
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_translatedHeartRepresentativeObjectIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      shift
      source
      degree) ×
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_translatedHeartRepresentativeObjectIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      shift
      target
      degree) //
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_translatedHeartRepresentativeMap
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      shift
      hom
      degree).2 } :=
  Subtype.mk
    (Prod.mk
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_translatedHeartRepresentativeObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        shift
        source
        degree)
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_translatedHeartRepresentativeObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        shift
        target
        degree))
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_translatedHeartRepresentativeMap
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      shift
      hom
      degree).2

end AnalyticMotives
end LFunctions
end Boundary
