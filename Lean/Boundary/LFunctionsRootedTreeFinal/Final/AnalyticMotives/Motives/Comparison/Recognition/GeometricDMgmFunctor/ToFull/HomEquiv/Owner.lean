import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.Owner

/-!
# Hom equivalence consequences for full recognition functors

This file records downstream-facing morphism consequences of the fully faithful
full Boundary-DMgm recognition functor transported from geometric recognition
data.
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

/-- The transported full-recognition hom equivalence is injective on source
morphisms. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_injective
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
    {source target : TraceAnalyticDMgmComparisonSource} :
    Function.Injective
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful :
        (source ⟶ target) ≃
          ((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
            (composition := composition) twistData homotopyFunctor inverts).obj source ⟶
          (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
            (composition := composition) twistData homotopyFunctor inverts).obj target)) :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful).injective

/-- The transported full-recognition hom equivalence is surjective onto target
morphisms. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_surjective
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
    {source target : TraceAnalyticDMgmComparisonSource} :
    Function.Surjective
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful :
        (source ⟶ target) ≃
          ((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
            (composition := composition) twistData homotopyFunctor inverts).obj source ⟶
          (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
            (composition := composition) twistData homotopyFunctor inverts).obj target)) :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful).surjective

/-- The transported full-recognition hom equivalence is bijective on hom
sets. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_bijective
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
    {source target : TraceAnalyticDMgmComparisonSource} :
    Function.Bijective
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful :
        (source ⟶ target) ≃
          ((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
            (composition := composition) twistData homotopyFunctor inverts).obj source ⟶
          (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
            (composition := composition) twistData homotopyFunctor inverts).obj target)) :=
  And.intro
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_injective
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful)
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_surjective
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful)

/-- Equality of full-recognition images is equivalent to equality of source
morphisms. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_map_eq_iff_of_geometric_fullyFaithful
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
    {source target : TraceAnalyticDMgmComparisonSource}
    {left right : source ⟶ target} :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).map left =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).map right ↔
      left = right :=
  Iff.intro
    (fun map_eq =>
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_map_injective_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        map_eq)
    (fun source_eq =>
      congrArg
        (fun morphism =>
          (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
            (composition := composition) twistData homotopyFunctor inverts).map morphism)
        source_eq)

/-- The transported full-recognition preimage respects equality of target
morphisms. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_preimage_congr_of_geometric_fullyFaithful
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
    {source target : TraceAnalyticDMgmComparisonSource}
    {left right :
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj source ⟶
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj target}
    (target_eq : left = right) :
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_preimage_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        left =
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_preimage_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        right :=
  congrArg
    (fun morphism =>
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_preimage_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        morphism)
    target_eq

end AnalyticMotives
end LFunctions
end Boundary
