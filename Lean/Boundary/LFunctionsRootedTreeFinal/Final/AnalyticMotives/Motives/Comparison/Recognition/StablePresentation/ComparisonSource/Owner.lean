import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableInfinity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.StablePresentation.Owner

/-!
# Stable-presentation recognition on the comparison source

The stable presentation of analytic motives presents the same category as the
analytic `DMgm` comparison source.  This file gives the stable-presentation
recognition functor a comparison-source name and records the definitional
identifications needed by downstream recognition theorems.
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

/-- The full Boundary-DMgm recognition functor, viewed directly as a functor
from the analytic comparison source carrying the stable-infinity package. -/
def comparisonSourceStableFullDMgmFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticDMgmComparisonSource ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticMotiveRecognition.stablePresentationFullDMgmFunctor
    (composition := composition)
    twistData
    homotopyFunctor
    inverts

/-- The comparison-source stable recognition functor is the
stable-presentation recognition functor. -/
theorem comparisonSourceStableFullDMgmFunctor_eq_stablePresentation
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticMotiveRecognition.comparisonSourceStableFullDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts =
      TraceAnalyticMotiveRecognition.stablePresentationFullDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts :=
  rfl

/-- The comparison-source stable recognition functor is the descended full
Boundary-DMgm recognition functor. -/
theorem comparisonSourceStableFullDMgmFunctor_eq_descended
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticMotiveRecognition.comparisonSourceStableFullDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts :=
  rfl

/-- Geometric full faithfulness transports to the comparison-source stable
recognition functor. -/
noncomputable def comparisonSourceStableFullDMgmFunctor_fullyFaithful
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
          .FullyFaithful) :
    (TraceAnalyticMotiveRecognition.comparisonSourceStableFullDMgmFunctor
      (composition := composition) twistData homotopyFunctor inverts)
        .FullyFaithful :=
  TraceAnalyticMotiveRecognition
    .stablePresentationFullDMgmFunctor_fullyFaithful
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful

/-- The comparison-source stable recognition functor has the complete bounded
weight-triangular package inherited from the stable-presentation recognition
functor. -/
def comparisonSourceStableFullDMgmFunctor_completeWeightTriangularBoundedMap
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
  TraceAnalyticMotiveRecognition
    .stablePresentationFullDMgmFunctor_completeWeightTriangularBoundedMap
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom

/-- The comparison-source stable recognition functor has the complete
heart-representative weight-triangular package inherited from the
stable-presentation recognition functor. -/
def comparisonSourceStableFullDMgmFunctor_completeWeightTriangularHeartRepresentativeMap
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
  TraceAnalyticMotiveRecognition
    .stablePresentationFullDMgmFunctor_completeWeightTriangularHeartRepresentativeMap
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom
      degree

end TraceAnalyticMotiveRecognition

end AnalyticMotives
end LFunctions
end Boundary
