import Boundary.EffectiveMotiveFunctor

/-!
# Boundary smooth-scheme carrier endpoint for effective realization

This file records the parent Boundary smooth-scheme endpoint that an analytic
trace-object carrier maps into before applying the canonical effective-motive
functor.
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
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- Boundary smooth schemes are the geometric carrier endpoint for analytic
effective realization. -/
abbrev TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrier :=
  Geometry.SmSchemeOver k

/-- Boundary effective motives are the effective-motive endpoint of a smooth
scheme carrier. -/
abbrev TraceAnalyticEffectiveRealization.boundaryEffectiveCarrierTarget :=
  canonicalEffectiveMotives composition

/-- The parent Boundary effective-motive functor evaluates a smooth-scheme
carrier. -/
def TraceAnalyticEffectiveRealization.boundaryEffectiveCarrier
    (scheme : TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrier (k := k)) :
    TraceAnalyticEffectiveRealization.boundaryEffectiveCarrierTarget
        (composition := composition) :=
  canonicalEffectiveMotive composition scheme

/-- The smooth-scheme carrier functor is the parent canonical effective motive
functor. -/
def TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor :
    TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrier (k := k) ⥤
      TraceAnalyticEffectiveRealization.boundaryEffectiveCarrierTarget
        (composition := composition) :=
  canonicalEffectiveMotiveFunctor composition hgraph

/-- Object formula for the Boundary smooth-scheme carrier functor. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor_obj
    (scheme : TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrier (k := k)) :
    (TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor
        (composition := composition) hgraph).obj scheme =
      TraceAnalyticEffectiveRealization.boundaryEffectiveCarrier
        (composition := composition) scheme :=
  rfl

/-- Map formula for the Boundary smooth-scheme carrier functor. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor_map
    {source target :
      TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrier (k := k)}
    (morphism : source ⟶ target) :
    (TraceAnalyticEffectiveRealization.boundarySmoothSchemeCarrierFunctor
        (composition := composition) hgraph).map morphism =
      canonicalEffectiveMotiveMap composition morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
