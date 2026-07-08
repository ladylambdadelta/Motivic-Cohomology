import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StablePresentation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.RecognitionTheorem.Owner

/-!
# Recognition from the stable analytic presentation

This file places the currently proved recognition theorem directly at the
stable-presentation boundary.  The source category is the category presented
by the stable analytic motive quasicategory, and the theorem surface records
the full Boundary-DMgm recognition functor, its transported full faithfulness,
and the existing complete weight-triangular packages.
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

/-- The full Boundary-DMgm recognition functor, viewed as a functor from the
category presented by the stable analytic motive quasicategory. -/
def TraceAnalyticMotiveRecognition.stablePresentationFullDMgmFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticStableMotiveQuasicategory.presentedCategory ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
    (composition := composition)
    twistData
    homotopyFunctor
    inverts

/-- The stable-presentation full recognition functor is the descended full
Boundary-DMgm recognition functor. -/
theorem TraceAnalyticMotiveRecognition.stablePresentationFullDMgmFunctor_eq_descended
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticMotiveRecognition.stablePresentationFullDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts :=
  rfl

/-- Geometric full faithfulness transports to full faithfulness of the
stable-presentation full Boundary-DMgm recognition functor. -/
noncomputable def TraceAnalyticMotiveRecognition.stablePresentationFullDMgmFunctor_fullyFaithful
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts).FullyFaithful) :
    (TraceAnalyticMotiveRecognition.stablePresentationFullDMgmFunctor
      (composition := composition) twistData homotopyFunctor inverts).FullyFaithful :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful

/-- The stable-presentation full recognition functor has the complete bounded
weight-triangular package already proved for the descended full recognition
functor. -/
def TraceAnalyticMotiveRecognition.stablePresentationFullDMgmFunctor_completeWeightTriangularBoundedMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
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
        target) :
    { objectData :
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_boundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        source) ×
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_boundedObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        target) //
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_boundedMap_weightTriangular
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom) } :=
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularBoundedMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful
    hom

/-- The stable-presentation full recognition functor has the complete exact
heart-representative weight-triangular package already proved for the
descended full recognition functor. -/
def TraceAnalyticMotiveRecognition.stablePresentationFullDMgmFunctor_completeWeightTriangularHeartRepresentativeMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
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
  TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularHeartRepresentativeMap
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful
    hom
    degree

end AnalyticMotives
end LFunctions
end Boundary
