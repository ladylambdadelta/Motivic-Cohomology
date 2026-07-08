import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.ParentBoundary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.BoundaryTarget.FromSmoothScheme.ComparisonTarget.Owner

/-!
# Parent Boundary formulas for the smooth-scheme comparison endpoint

This file records the parent `DMgm` names for the smooth-scheme endpoint used
by analytic effective realization.  The endpoint remains the parent Boundary
effective-motive functor followed by the parent Boundary `DMgm` embedding.
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

/-- The smooth-scheme comparison endpoint is the parent Boundary
smooth-scheme-to-`DMgm` endpoint. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_eq_parentBoundaryDMgmFunctor :
    TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
        (composition := composition) hgraph =
      TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor
        (composition := composition) hgraph :=
  rfl

/-- The smooth-scheme comparison endpoint is the parent canonical effective
motive functor followed by the parent Boundary `DMgm` effective embedding. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_eq_parentEffective_comp_parentDMgmEmbedding :
    TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
        (composition := composition) hgraph =
      Boundary.canonicalEffectiveMotiveFunctor composition hgraph ⋙
        Boundary.VoevodskyDMgmEffectiveEmbedding
          (composition := composition) :=
  rfl

/-- Object formula using the parent Boundary `DMgm` effective embedding. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_obj_parentBoundary
    (scheme : Geometry.SmSchemeOver k) :
    (TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
        (composition := composition) hgraph).obj scheme =
      (Boundary.VoevodskyDMgmEffectiveEmbedding
        (composition := composition)).obj
        (canonicalEffectiveMotive composition scheme) :=
  rfl

/-- Map formula using the parent Boundary `DMgm` effective embedding. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_map_parentBoundary
    {source target : Geometry.SmSchemeOver k}
    (morphism : source ⟶ target) :
    (TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
        (composition := composition) hgraph).map morphism =
      (Boundary.VoevodskyDMgmEffectiveEmbedding
        (composition := composition)).map
        (canonicalEffectiveMotiveMap composition morphism) :=
  rfl

/-- The parent Boundary effective object formula for the smooth-scheme
comparison endpoint. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_obj_parentBoundary_effectiveObj
    (scheme : Geometry.SmSchemeOver k) :
    ((TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
        (composition := composition) hgraph).obj scheme).effectiveObj =
      canonicalEffectiveMotive composition scheme :=
  rfl

/-- The parent Boundary Tate-degree formula for the smooth-scheme comparison
endpoint. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_obj_parentBoundary_tateTwist
    (scheme : Geometry.SmSchemeOver k) :
    ((TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
        (composition := composition) hgraph).obj scheme).tateTwist =
      0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
