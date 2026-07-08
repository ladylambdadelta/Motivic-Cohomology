import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.BoundaryTarget.Owner

/-!
# Smooth-scheme endpoint in the parent Boundary DMgm target

This file composes the parent Boundary effective-motive functor with the
parent Boundary `DMgm` embedding.  It is the concrete target-side endpoint for
an algebraization of a certified analytic trace object.
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

/-- The parent Boundary functor from smooth schemes directly into the
`DMgm` comparison target. -/
def TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor :
    Geometry.SmSchemeOver k ⥤
      Boundary.VoevodskyDMgmQ_Q (composition := composition) :=
  TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor
      (composition := composition) hgraph ⋙
    TraceAnalyticEffectiveRealization.boundaryDMgmEmbedding
      (composition := composition)

/-- The smooth-scheme-to-`DMgm` functor is the parent effective functor followed
by the parent effective embedding. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor_eq_comp :
    TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor
        (composition := composition) hgraph =
      TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor
          (composition := composition) hgraph ⋙
        TraceAnalyticEffectiveRealization.boundaryDMgmEmbedding
          (composition := composition) :=
  rfl

/-- Object formula for the smooth-scheme-to-`DMgm` endpoint. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor_obj
    (scheme : Geometry.SmSchemeOver k) :
    (TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor
        (composition := composition) hgraph).obj scheme =
      (TraceAnalyticEffectiveRealization.boundaryDMgmEmbedding
        (composition := composition)).obj
        (canonicalEffectiveMotive composition scheme) :=
  rfl

/-- Map formula for the smooth-scheme-to-`DMgm` endpoint. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor_map
    {source target : Geometry.SmSchemeOver k}
    (morphism : source ⟶ target) :
    (TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor
        (composition := composition) hgraph).map morphism =
      (TraceAnalyticEffectiveRealization.boundaryDMgmEmbedding
        (composition := composition)).map
        (canonicalEffectiveMotiveMap composition morphism) :=
  rfl

/-- The effective object of a smooth scheme inside the `DMgm` endpoint is its
canonical effective motive. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor_obj_effectiveObj
    (scheme : Geometry.SmSchemeOver k) :
    ((TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor
        (composition := composition) hgraph).obj scheme).effectiveObj =
      canonicalEffectiveMotive composition scheme :=
  rfl

/-- A smooth scheme enters the `DMgm` endpoint in Tate degree zero. -/
theorem TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor_obj_tateTwist
    (scheme : Geometry.SmSchemeOver k) :
    ((TraceAnalyticEffectiveRealization.boundarySmoothSchemeDMgmFunctor
        (composition := composition) hgraph).obj scheme).tateTwist =
      0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
