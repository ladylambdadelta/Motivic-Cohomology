import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Target.Geometric.SmoothScheme.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Target.Geometric.TateStabilization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Target.TateStabilization.Owner

/-!
# Functor from the geometric Boundary target to the full Boundary DMgm target

This file constructs the comparison functor from geometric Tate-stabilized
Boundary motives to the full Tate-stabilized Boundary DMgm target by the formal
Tate-stabilization extension API.
-/

universe u

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
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

/-- Extension data sending geometric effective motives, in each Tate degree,
to the corresponding full Boundary DMgm object. -/
def TraceAnalyticMotiveComparison.geometricToFullTargetExtension :
    TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension
      (composition := composition)
      twistData
      (TraceAnalyticDMgmComparisonTarget (composition := composition)) where
  obj object degree := ⟨object.1, degree⟩
  map hom sourceDegree targetDegree := hom
  map_id object degree := rfl
  map_comp left right sourceDegree middleDegree targetDegree := rfl

/-- Object formula for the geometric-to-full extension data. -/
theorem TraceAnalyticMotiveComparison.geometricToFullTargetExtension_obj
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition))
    (degree : ℤ) :
    (TraceAnalyticMotiveComparison.geometricToFullTargetExtension
      (composition := composition) twistData).obj object degree =
      (⟨object.1, degree⟩ :
        TraceAnalyticDMgmComparisonTarget (composition := composition)) :=
  rfl

/-- Map formula for the geometric-to-full extension data. -/
theorem TraceAnalyticMotiveComparison.geometricToFullTargetExtension_map
    {source target :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)}
    (hom : source ⟶ target)
    (sourceDegree targetDegree : ℤ) :
    (TraceAnalyticMotiveComparison.geometricToFullTargetExtension
      (composition := composition) twistData).map
        hom sourceDegree targetDegree =
      hom :=
  rfl

/-- The functor from the geometric Boundary target to the full Boundary DMgm
target induced by formal Tate stabilization. -/
def TraceAnalyticMotiveComparison.geometricToFullTargetFunctor :
    TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension.lift
    (composition := composition)
    twistData
    (TraceAnalyticMotiveComparison.geometricToFullTargetExtension
      (composition := composition) twistData)

/-- The geometric-to-full functor is the formal lift of the geometric-to-full
extension data. -/
theorem TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_eq_lift :
    TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData =
      TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension.lift
        (composition := composition)
        twistData
        (TraceAnalyticMotiveComparison.geometricToFullTargetExtension
          (composition := composition) twistData) :=
  rfl

/-- Object formula for the geometric-to-full target functor. -/
theorem TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_obj
    (object :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData) :
    (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
      (composition := composition) twistData).obj object =
      (⟨object.effectiveObj.1, object.tateTwist⟩ :
        TraceAnalyticDMgmComparisonTarget (composition := composition)) :=
  rfl

/-- Map formula for the geometric-to-full target functor. -/
theorem TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_map
    {source target :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
      (composition := composition) twistData).map hom =
      hom :=
  rfl

/-- The geometric-to-full target functor is full: morphisms in the full target
between geometric objects are the same underlying effective-motive maps. -/
instance TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_full :
    (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
      (composition := composition) twistData).Full where
  map_surjective {X Y} morphism :=
    Exists.intro morphism rfl

/-- The geometric-to-full target functor is faithful because it is
definitionally the identity on the underlying stabilized morphisms. -/
instance TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_faithful :
    (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
      (composition := composition) twistData).Faithful where
  map_injective {X Y} {left right} map_eq :=
    map_eq

/-- Explicit fully faithful package for the geometric-to-full target functor. -/
def TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_fullyFaithful :
    (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
      (composition := composition) twistData).FullyFaithful where
  preimage {X Y} morphism := morphism
  map_preimage {X Y} morphism := rfl
  preimage_map {X Y} morphism := rfl

/-- The geometric-to-full target preimage is the same underlying stabilized
morphism. -/
theorem TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_preimage_eq
    {source target :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData}
    (morphism :
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj source ⟶
        (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData).obj target) :
    (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_fullyFaithful
      (composition := composition) twistData).preimage morphism =
      morphism :=
  rfl

/-- The geometric-to-full target preimage is a right inverse to map on
morphisms. -/
theorem TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_map_preimage
    {source target :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData}
    (morphism :
      (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj source ⟶
        (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData).obj target) :
    (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
      (composition := composition) twistData).map
        ((TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_fullyFaithful
          (composition := composition) twistData).preimage morphism) =
      morphism :=
  rfl

/-- The geometric-to-full target preimage is a left inverse to map on
morphisms. -/
theorem TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_preimage_map
    {source target :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData}
    (morphism : source ⟶ target) :
    (TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_fullyFaithful
      (composition := composition) twistData).preimage
        ((TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
          (composition := composition) twistData).map morphism) =
      morphism :=
  rfl

/-- The geometric-to-full functor sends an embedded geometric effective motive
to the full target object with the same underlying effective motive in Tate
degree zero. -/
theorem TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_effectiveEmbedding_obj
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    ((TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
        (composition := composition) twistData) ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj object =
      (⟨object.1, 0⟩ :
        TraceAnalyticDMgmComparisonTarget (composition := composition)) :=
  rfl

/-- The geometric-to-full functor sends embedded geometric effective morphisms
to the same underlying effective morphisms in the full target. -/
theorem TraceAnalyticMotiveComparison.geometricToFullTargetFunctor_effectiveEmbedding_map
    {source target :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)}
    (hom : source ⟶ target) :
    ((TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
        (composition := composition) twistData) ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map hom =
      hom :=
  rfl

/-- The geometric smooth-scheme endpoint followed by the geometric-to-full
functor has the same object formula as the full smooth-scheme endpoint. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeGeometricToFullTargetFunctor_obj
    (scheme : Geometry.SmSchemeOver k) :
    (TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor
        (composition := composition) hgraph twistData ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).obj scheme =
      (TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor
        (composition := composition) hgraph).obj scheme :=
  rfl

/-- The geometric smooth-scheme endpoint followed by the geometric-to-full
functor has the same map formula as the full smooth-scheme endpoint. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeGeometricToFullTargetFunctor_map
    {source target : Geometry.SmSchemeOver k}
    (morphism : source ⟶ target) :
    (TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor
        (composition := composition) hgraph twistData ⋙
      TraceAnalyticMotiveComparison.geometricToFullTargetFunctor
        (composition := composition) twistData).map morphism =
      (TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor
        (composition := composition) hgraph).map morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
