import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.StablePresentation.Owner

/-!
# Projections from stable-presentation recognition packages

This file names the projections from the stable-presentation complete bounded
and heart-representative weight-triangular packages.
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

namespace TraceAnalyticMotiveRecognition

/-- Source object data projected from the stable-presentation complete bounded
package. -/
theorem stablePresentationCompleteWeightTriangularBoundedMap_sourceObjectData
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts)
          .FullyFaithful)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveRecognition
      .stablePresentationFullDMgmFunctor_completeWeightTriangularBoundedMap
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        hom).1.1 =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_boundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        source :=
  rfl

/-- Target object data projected from the stable-presentation complete bounded
package. -/
theorem stablePresentationCompleteWeightTriangularBoundedMap_targetObjectData
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts)
          .FullyFaithful)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveRecognition
      .stablePresentationFullDMgmFunctor_completeWeightTriangularBoundedMap
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        hom).1.2 =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_boundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        target :=
  rfl

/-- Naturality projected from the stable-presentation complete bounded
package. -/
theorem stablePresentationCompleteWeightTriangularBoundedMap_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts)
          .FullyFaithful)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveRecognition
      .stablePresentationFullDMgmFunctor_completeWeightTriangularBoundedMap
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        hom).2 =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_boundedMap_weightTriangular
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        hom :=
  rfl

/-- Source object data projected from the stable-presentation complete
heart-representative package. -/
theorem stablePresentationCompleteWeightTriangularHeartRepresentativeMap_sourceObjectData
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts)
          .FullyFaithful)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    (TraceAnalyticMotiveRecognition
      .stablePresentationFullDMgmFunctor_completeWeightTriangularHeartRepresentativeMap
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        hom
        degree).1.1 =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_heartRepresentativeObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        source
        degree :=
  rfl

/-- Target object data projected from the stable-presentation complete
heart-representative package. -/
theorem stablePresentationCompleteWeightTriangularHeartRepresentativeMap_targetObjectData
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts)
          .FullyFaithful)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    (TraceAnalyticMotiveRecognition
      .stablePresentationFullDMgmFunctor_completeWeightTriangularHeartRepresentativeMap
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        hom
        degree).1.2 =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_heartRepresentativeObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        target
        degree :=
  rfl

/-- Naturality projected from the stable-presentation complete
heart-representative package. -/
theorem stablePresentationCompleteWeightTriangularHeartRepresentativeMap_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts)
          .FullyFaithful)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target)
    (degree : ℤ) :
    (TraceAnalyticMotiveRecognition
      .stablePresentationFullDMgmFunctor_completeWeightTriangularHeartRepresentativeMap
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        hom
        degree).2 =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_heartRepresentativeMap
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        hom
        degree).2 :=
  rfl

end TraceAnalyticMotiveRecognition

end AnalyticMotives
end LFunctions
end Boundary
