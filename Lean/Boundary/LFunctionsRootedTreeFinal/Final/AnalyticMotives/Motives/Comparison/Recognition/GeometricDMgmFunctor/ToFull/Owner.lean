import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Target.Geometric.ToFull.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmFunctor.Descent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.Descent.Owner

/-!
# Full Boundary-DMgm recognition functors from geometric recognition data

This file turns a null-inverting homotopy-level functor into the geometric
Boundary target into a full Boundary-DMgm recognition functor by postcomposing
with the geometric-to-full target functor.
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

/-- Postcomposition with the geometric-to-full target functor preserves the
stable null-inversion condition. -/
theorem TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
      (homotopyFunctor ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData) :=
  MorphismProperty.IsInvertedBy.of_comp
    TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms
    homotopyFunctor
    inverts
    (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
      (composition := composition) twistData)

/-- Full Boundary-DMgm recognition functor induced from geometric homotopy-level
recognition data by postcomposition with the geometric-to-full target functor. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticDMgmComparisonSource ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticMotiveRecognition.descendedDMgmFunctor
    (composition := composition)
    (homotopyFunctor ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition) twistData homotopyFunctor inverts)

/-- The full recognition functor from geometric data is the ordinary full
Boundary-DMgm descent of the postcomposed homotopy-level functor. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_eq_descended
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts =
      TraceAnalyticMotiveRecognition.descendedDMgmFunctor
        (composition := composition)
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData)
        (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
          (composition := composition) twistData homotopyFunctor inverts) :=
  rfl

/-- The full recognition functor from geometric data is isomorphic to the
geometric descended recognition functor followed by the geometric-to-full
target functor. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_postcomposeIso
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts ≅
      TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData :=
  TraceAnalyticStableHomotopyComparisonSource.liftPostcomposeIso
    homotopyFunctor
    inverts
    (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
      (composition := composition) twistData)

/-- Fullness of the geometric descended recognition functor transports to the
full Boundary-DMgm recognition functor induced from it. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_full_of_geometric_full
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    [Functor.Full
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts)] :
    Functor.Full
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts) :=
  Functor.Full.of_iso
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_postcomposeIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).symm

/-- Faithfulness of the geometric descended recognition functor transports to
the full Boundary-DMgm recognition functor induced from it. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_faithful_of_geometric_faithful
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    [Functor.Faithful
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts)] :
    Functor.Faithful
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts) :=
  Functor.Faithful.of_iso
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_postcomposeIso
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).symm

/-- Fully faithfulness of the geometric descended recognition functor
transports to the full Boundary-DMgm recognition functor induced from it. -/
noncomputable def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts).FullyFaithful) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition) twistData homotopyFunctor inverts).FullyFaithful :=
  letI geometricFull :
      Functor.Full
        (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
          (composition := composition) twistData homotopyFunctor inverts) :=
    geometricFullyFaithful.full
  letI geometricFaithful :
      Functor.Faithful
        (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
          (composition := composition) twistData homotopyFunctor inverts) :=
    geometricFullyFaithful.faithful
  letI fullTarget :
      Functor.Full
        (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
          (composition := composition) twistData homotopyFunctor inverts) :=
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_full_of_geometric_full
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
  letI faithfulTarget :
      Functor.Faithful
        (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
          (composition := composition) twistData homotopyFunctor inverts) :=
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_faithful_of_geometric_faithful
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
  Functor.FullyFaithful.ofFullyFaithful
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition) twistData homotopyFunctor inverts)

/-- Hom equivalence for the full Boundary-DMgm recognition functor transported
from a fully faithful geometric descended recognition functor. -/
noncomputable def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
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
    (source ⟶ target) ≃
      ((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj source ⟶
        (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
          (composition := composition) twistData homotopyFunctor inverts).obj target) :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful).homEquiv

/-- The transported full Boundary-DMgm recognition hom map is injective. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_map_injective_of_geometric_fullyFaithful
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
    {left right : source ⟶ target}
    (map_eq :
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).map left =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).map right) :
    left = right :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful).map_injective map_eq

/-- The transported full Boundary-DMgm recognition hom map is surjective. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_map_surjective_of_geometric_fullyFaithful
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
      ((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).map :
        (source ⟶ target) →
          ((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
            (composition := composition) twistData homotopyFunctor inverts).obj source ⟶
            (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
              (composition := composition) twistData homotopyFunctor inverts).obj target)) :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful).map_surjective

/-- The transported full Boundary-DMgm recognition hom map is bijective. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_map_bijective_of_geometric_fullyFaithful
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
    (source target : TraceAnalyticDMgmComparisonSource) :
    Function.Bijective
      ((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).map :
        (source ⟶ target) →
          ((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
            (composition := composition) twistData homotopyFunctor inverts).obj source ⟶
            (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
              (composition := composition) twistData homotopyFunctor inverts).obj target)) :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful).map_bijective source target

/-- The transported hom equivalence sends a source morphism to its image under
the full Boundary-DMgm recognition functor. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_apply
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
    (morphism : source ⟶ target) :
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        morphism =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).map
        morphism :=
  rfl

/-- The inverse of the transported hom equivalence is the fully faithful
preimage for the full Boundary-DMgm recognition functor. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_symm_apply
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
    (morphism :
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj source ⟶
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj target) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful).symm morphism =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful).preimage morphism :=
  rfl

/-- The transported hom equivalence recovers source morphisms after applying
the full Boundary-DMgm recognition functor. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_left_inverse
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
    (morphism : source ⟶ target) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful).symm
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        morphism) =
      morphism :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful).left_inv morphism

/-- The transported hom equivalence recovers target morphisms after applying
its inverse preimage. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_right_inverse
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
    (morphism :
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj source ⟶
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj target) :
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
      ((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful).symm morphism) =
      morphism :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful).right_inv morphism

/-- Fully faithful preimage for the full Boundary-DMgm recognition functor
transported from geometric recognition data. -/
noncomputable def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_preimage_of_geometric_fullyFaithful
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
    (morphism :
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj source ⟶
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj target) :
    source ⟶ target :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful).preimage morphism

/-- The named full-recognition preimage is the inverse of the transported hom
equivalence. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_preimage_eq_homEquiv_symm
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
    (morphism :
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj source ⟶
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj target) :
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_preimage_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        morphism =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful).symm morphism :=
  Eq.symm
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_homEquiv_symm_apply
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      morphism)

/-- The full Boundary-DMgm recognition functor maps its transported preimage
back to the original target morphism. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_map_preimage_of_geometric_fullyFaithful
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
    (morphism :
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj source ⟶
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
        (composition := composition) twistData homotopyFunctor inverts).obj target) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition) twistData homotopyFunctor inverts).map
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_preimage_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        morphism) =
      morphism :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful).map_preimage morphism

/-- The transported preimage of a full Boundary-DMgm recognition image recovers
the original source morphism. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_preimage_map_of_geometric_fullyFaithful
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
    (morphism : source ⟶ target) :
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_preimage_of_geometric_fullyFaithful
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        geometricFullyFaithful
        ((TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
          (composition := composition) twistData homotopyFunctor inverts).map
          morphism) =
      morphism :=
  (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_of_geometric_fullyFaithful
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    geometricFullyFaithful).preimage_map morphism

/-- Object comparison isomorphism for the full recognition functor induced
from geometric data. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).obj
        (TraceAnalyticStableHomotopyComparisonSource.objectOf object) ≅
      (homotopyFunctor ⋙
        TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData).obj object :=
  TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
    (composition := composition)
    (homotopyFunctor ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition) twistData homotopyFunctor inverts)
    object

/-- The object comparison isomorphism from geometric data is the full descent
object comparison for the postcomposed homotopy-level functor. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso_eq_descended
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition) twistData homotopyFunctor inverts object =
      TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
        (composition := composition)
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData)
        (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
          (composition := composition) twistData homotopyFunctor inverts)
        object :=
  rfl

/-- Projection formula for the full Boundary-DMgm recognition functor induced
from geometric data on a staged rewrite-generator map. -/
theorem TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_rewriteGeneratorStage_naturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (generator : TraceRewriteGenerator) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            generator)) ≫
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          generator.targetObject)).hom =
      (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometricObjectIso
        (composition := composition)
        twistData
        homotopyFunctor
        inverts
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          generator.sourceObject)).hom ≫
        (homotopyFunctor ⋙
          TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
            (composition := composition) twistData).map
          (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
            generator) :=
  TraceAnalyticMotiveRecognition.descendedDMgmFunctor_rewriteGeneratorStage_naturality
    (composition := composition)
    (homotopyFunctor ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData)
    (TraceAnalyticMotiveRecognition.geometricToFullTargetFunctor_preservesInverted
      (composition := composition) twistData homotopyFunctor inverts)
    generator

end AnalyticMotives
end LFunctions
end Boundary
