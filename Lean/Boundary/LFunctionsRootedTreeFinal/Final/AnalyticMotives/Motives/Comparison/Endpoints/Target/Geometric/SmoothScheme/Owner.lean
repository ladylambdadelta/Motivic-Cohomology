import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Target.Geometric.Formulas.Owner

/-!
# Smooth-scheme endpoint for the geometric Boundary DMgm target

This file sends Boundary smooth schemes first to geometric effective motives
and then to the geometric Tate-stabilized Boundary motive target.
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

/-- Smooth schemes enter the geometric effective motive category by their
canonical effective motive objects. -/
def TraceAnalyticMotiveComparison.smoothSchemeGeometricEffectiveFunctor :
    Geometry.SmSchemeOver k ⥤
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition) where
  obj scheme := canonicalGeometricEffectiveMotiveObject composition scheme
  map morphism := canonicalEffectiveMotiveMap composition morphism
  map_id scheme := canonicalEffectiveMotiveMap_id composition scheme
  map_comp left right :=
    canonicalEffectiveMotiveMap_comp composition hgraph left right

/-- Object formula for the smooth-scheme geometric effective endpoint. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeGeometricEffectiveFunctor_obj
    (scheme : Geometry.SmSchemeOver k) :
    (TraceAnalyticMotiveComparison.smoothSchemeGeometricEffectiveFunctor
        (composition := composition) hgraph).obj scheme =
      canonicalGeometricEffectiveMotiveObject composition scheme :=
  rfl

/-- The underlying effective motive of the smooth-scheme geometric effective
endpoint is the canonical effective motive used by the full target endpoint. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeGeometricEffectiveFunctor_obj_val
    (scheme : Geometry.SmSchemeOver k) :
    ((TraceAnalyticMotiveComparison.smoothSchemeGeometricEffectiveFunctor
        (composition := composition) hgraph).obj scheme).1 =
      canonicalEffectiveMotive composition scheme :=
  rfl

/-- Map formula for the smooth-scheme geometric effective endpoint. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeGeometricEffectiveFunctor_map
    {source target : Geometry.SmSchemeOver k}
    (morphism : source ⟶ target) :
    (TraceAnalyticMotiveComparison.smoothSchemeGeometricEffectiveFunctor
        (composition := composition) hgraph).map morphism =
      canonicalEffectiveMotiveMap composition morphism :=
  rfl

/-- The smooth-scheme geometric effective endpoint map is the canonical
effective-motive map after including the full subcategory of geometric
effective motives into all effective motives. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeGeometricEffectiveFunctor_inclusion_map
    {source target : Geometry.SmSchemeOver k}
    (morphism : source ⟶ target) :
    (canonicalGeometricEffectiveMotivesInclusion composition).map
        ((TraceAnalyticMotiveComparison.smoothSchemeGeometricEffectiveFunctor
          (composition := composition) hgraph).map morphism) =
      canonicalEffectiveMotiveMap composition morphism :=
  rfl

/-- Smooth schemes enter the geometric Boundary target by geometric effective
embedding in Tate degree zero. -/
def TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor :
    Geometry.SmSchemeOver k ⥤
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData :=
  TraceAnalyticMotiveComparison.smoothSchemeGeometricEffectiveFunctor
      (composition := composition) hgraph ⋙
    TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
      (composition := composition) twistData

/-- The smooth-scheme geometric target endpoint is geometric effective
realization followed by the geometric effective embedding. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor_eq_comp :
    TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor
        (composition := composition) hgraph twistData =
      TraceAnalyticMotiveComparison.smoothSchemeGeometricEffectiveFunctor
          (composition := composition) hgraph ⋙
        TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
          (composition := composition) twistData :=
  rfl

/-- Object formula for the smooth-scheme geometric target endpoint. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor_obj
    (scheme : Geometry.SmSchemeOver k) :
    (TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor
        (composition := composition) hgraph twistData).obj scheme =
      (TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
        (composition := composition) twistData).obj
        (canonicalGeometricEffectiveMotiveObject composition scheme) :=
  rfl

/-- Map formula for the smooth-scheme geometric target endpoint. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor_map
    {source target : Geometry.SmSchemeOver k}
    (morphism : source ⟶ target) :
    (TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor
        (composition := composition) hgraph twistData).map morphism =
      (TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
        (composition := composition) twistData).map
        (canonicalEffectiveMotiveMap composition morphism) :=
  rfl

/-- The effective object of a smooth scheme in the geometric target is its
canonical geometric effective motive. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor_obj_effectiveObj
    (scheme : Geometry.SmSchemeOver k) :
    ((TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor
        (composition := composition) hgraph twistData).obj scheme).effectiveObj =
      canonicalGeometricEffectiveMotiveObject composition scheme :=
  rfl

/-- The underlying effective motive of a smooth scheme in the geometric target
is the same canonical effective motive used by the full smooth-scheme target
endpoint. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor_obj_effectiveObj_val
    (scheme : Geometry.SmSchemeOver k) :
    (((TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor
        (composition := composition) hgraph twistData).obj scheme).effectiveObj).1 =
      canonicalEffectiveMotive composition scheme :=
  rfl

/-- A smooth scheme enters the geometric target in Tate degree zero. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor_obj_tateTwist
    (scheme : Geometry.SmSchemeOver k) :
    ((TraceAnalyticMotiveComparison.smoothSchemeGeometricTargetFunctor
        (composition := composition) hgraph twistData).obj scheme).tateTwist =
      0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
