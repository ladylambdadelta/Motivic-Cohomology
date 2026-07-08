import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.BoundaryTarget.FromSmoothScheme.Owner

/-!
# Smooth-scheme endpoint retargeted to the analytic DMgm comparison target

This file records that the smooth-scheme endpoint constructed from the parent
Boundary effective-motive functor lands in the analytic comparison target
alias, not in a separate target category.
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

/-- The smooth-scheme endpoint as a functor into the analytic comparison target
alias. -/
def TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor :
    Geometry.SmSchemeOver k ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor
    (composition := composition) hgraph

/-- Retargeting to the analytic comparison target is definitional. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_eq_parent :
    TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
        (composition := composition) hgraph =
      TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor
        (composition := composition) hgraph :=
  rfl

/-- Object formula for the smooth-scheme endpoint into the analytic comparison
target. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_obj
    (scheme : Geometry.SmSchemeOver k) :
    (TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
        (composition := composition) hgraph).obj scheme =
      (TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition)).obj
        (canonicalEffectiveMotive composition scheme) :=
  rfl

/-- Map formula for the smooth-scheme endpoint into the analytic comparison
target. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_map
    {source target : Geometry.SmSchemeOver k}
    (morphism : source ⟶ target) :
    (TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
        (composition := composition) hgraph).map morphism =
      (TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition)).map
        (canonicalEffectiveMotiveMap composition morphism) :=
  rfl

/-- The effective object of a smooth scheme in the comparison target is its
canonical effective motive. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_obj_effectiveObj
    (scheme : Geometry.SmSchemeOver k) :
    ((TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
        (composition := composition) hgraph).obj scheme).effectiveObj =
      canonicalEffectiveMotive composition scheme :=
  rfl

/-- A smooth scheme enters the comparison target in Tate degree zero. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor_obj_tateTwist
    (scheme : Geometry.SmSchemeOver k) :
    ((TraceAnalyticEffectiveRealization.boundarySmoothSchemeComparisonTargetFunctor
        (composition := composition) hgraph).obj scheme).tateTwist =
      0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
