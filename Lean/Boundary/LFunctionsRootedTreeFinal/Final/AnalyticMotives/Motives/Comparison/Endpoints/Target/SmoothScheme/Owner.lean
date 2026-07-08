import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.BoundaryTarget.FromSmoothScheme.Summary.Owner

/-!
# Smooth-scheme formulas for the comparison target endpoint

This file exposes the smooth-scheme-to-`DMgm` endpoint under the comparison
namespace.  The functor is the effective-realization smooth-scheme comparison
target functor.
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

/-- Endpoint functor from Boundary smooth schemes to the analytic comparison
target. -/
def TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor :
    Geometry.SmSchemeOver k ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
    (composition := composition) hgraph

/-- The endpoint smooth-scheme functor is the effective-realization
smooth-scheme comparison-target functor. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor_eq_effectiveRealization :
    TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor
        (composition := composition) hgraph =
      TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
        (composition := composition) hgraph :=
  rfl

/-- The endpoint smooth-scheme functor is the parent canonical effective motive
functor followed by the parent `DMgm` effective embedding. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor_eq_parentEffective_comp_parentDMgmEmbedding :
    TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor
        (composition := composition) hgraph =
      Boundary.canonicalEffectiveMotiveFunctor composition hgraph ⋙
        Boundary.VoevodskyDMgmEffectiveEmbedding
          (composition := composition) :=
  TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_eq_parentEffective_comp_parentDMgmEmbedding
    (composition := composition)
    hgraph

/-- The endpoint smooth-scheme functor is the analytic-name effective target
functor followed by the analytic-name comparison-target effective embedding. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor_eq_boundaryEffective_comp_comparisonTargetEmbedding :
    TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor
        (composition := composition) hgraph =
      TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor
          (composition := composition) hgraph ⋙
        TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
          (composition := composition) :=
  rfl

/-- The endpoint smooth-scheme functor is the analytic-name effective target
functor followed by the parent Boundary `DMgm` effective embedding. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor_eq_boundaryEffective_comp_parentDMgmEmbedding :
    TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor
        (composition := composition) hgraph =
      TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor
          (composition := composition) hgraph ⋙
        Boundary.VoevodskyDMgmEffectiveEmbedding
          (composition := composition) :=
  rfl

/-- The endpoint smooth-scheme functor is the parent effective target functor
followed by the analytic-name comparison-target effective embedding. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor_eq_parentEffective_comp_comparisonTargetEmbedding :
    TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor
        (composition := composition) hgraph =
      Boundary.canonicalEffectiveMotiveFunctor composition hgraph ⋙
        TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
          (composition := composition) :=
  rfl

/-- Object formula for the endpoint smooth-scheme target functor. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor_obj
    (scheme : Geometry.SmSchemeOver k) :
    (TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor
        (composition := composition) hgraph).obj scheme =
      (TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition)).obj
        (canonicalEffectiveMotive composition scheme) :=
  TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_obj
    (composition := composition)
    hgraph
    scheme

/-- Map formula for the endpoint smooth-scheme target functor. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor_map
    {source target : Geometry.SmSchemeOver k}
    (morphism : source ⟶ target) :
    (TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor
        (composition := composition) hgraph).map morphism =
      (TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition)).map
        (canonicalEffectiveMotiveMap composition morphism) :=
  TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_map
    (composition := composition)
    hgraph
    morphism

/-- Effective-object formula for the endpoint smooth-scheme target functor. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor_obj_effectiveObj
    (scheme : Geometry.SmSchemeOver k) :
    ((TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor
        (composition := composition) hgraph).obj scheme).effectiveObj =
      canonicalEffectiveMotive composition scheme :=
  TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_obj_effectiveObj
    (composition := composition)
    hgraph
    scheme

/-- Tate-degree formula for the endpoint smooth-scheme target functor. -/
theorem TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor_obj_tateTwist
    (scheme : Geometry.SmSchemeOver k) :
    ((TraceAnalyticMotiveComparison.smoothSchemeTargetFunctor
        (composition := composition) hgraph).obj scheme).tateTwist =
      0 :=
  TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_obj_tateTwist
    (composition := composition)
    hgraph
    scheme

end AnalyticMotives
end LFunctions
end Boundary
