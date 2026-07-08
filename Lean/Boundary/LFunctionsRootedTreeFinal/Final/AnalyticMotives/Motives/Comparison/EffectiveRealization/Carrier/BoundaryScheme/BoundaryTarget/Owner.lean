import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.BoundaryScheme.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.BoundaryTarget.Owner

/-!
# Compatibility of carrier and target smooth-scheme effective functors

This file records that the carrier-side smooth-scheme functor and the
target-side Boundary effective-motive functor are the same parent Boundary
canonical effective-motive functor.
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

/-- The carrier-side smooth-scheme functor is the target-side Boundary
effective-motive functor. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor_eq_boundaryTarget :
    TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor
        (composition := composition) hgraph =
      TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor
        (composition := composition) hgraph :=
  rfl

/-- The carrier-side smooth-scheme functor is the parent Boundary canonical
effective-motive functor. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor_eq_parent :
    TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor
        (composition := composition) hgraph =
      Boundary.canonicalEffectiveMotiveFunctor composition hgraph :=
  rfl

/-- Carrier-side and target-side object formulas agree on smooth schemes. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor_obj_eq_boundaryTarget_obj
    (scheme : Geometry.SmSchemeOver k) :
    (TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor
        (composition := composition) hgraph).obj scheme =
      (TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor
        (composition := composition) hgraph).obj scheme :=
  rfl

/-- Carrier-side and target-side map formulas agree on smooth-scheme
morphisms. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor_map_eq_boundaryTarget_map
    {source target : Geometry.SmSchemeOver k}
    (morphism : source ⟶ target) :
    (TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor
        (composition := composition) hgraph).map morphism =
      (TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor
        (composition := composition) hgraph).map morphism :=
  rfl

/-- Carrier-side effective evaluation agrees with the target-side object
formula. -/
theorem TraceAnalyticEffectiveRealization.boundaryEffectiveCarrier_eq_boundaryTarget_obj
    (scheme : Geometry.SmSchemeOver k) :
    TraceAnalyticEffectiveRealization.boundaryEffectiveCarrier
        (composition := composition) scheme =
      (TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor
        (composition := composition) hgraph).obj scheme :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
