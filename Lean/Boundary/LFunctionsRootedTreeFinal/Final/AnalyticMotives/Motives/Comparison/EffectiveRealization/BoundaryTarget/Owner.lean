import Boundary.DMgm

/-!
# Parent Boundary effective target for analytic realization

This file records the effective-motive target already supplied by the parent
Boundary construction.  These names are the target endpoint for comparing
certified trace representables before applying the existing `DMgm` embedding.
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

/-- Parent Boundary effective motive functor from smooth schemes. -/
def TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor :
    Geometry.SmSchemeOver k ⥤ canonicalEffectiveMotives composition :=
  Boundary.canonicalEffectiveMotiveFunctor composition hgraph

/-- The Boundary effective target functor is the parent canonical effective
motive functor. -/
theorem TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor_eq_parent :
    TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor
        (composition := composition) hgraph =
      Boundary.canonicalEffectiveMotiveFunctor composition hgraph :=
  rfl

/-- Object formula for the parent Boundary effective motive functor. -/
theorem TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor_obj
    (scheme : Geometry.SmSchemeOver k) :
    (TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor
        (composition := composition) hgraph).obj scheme =
      canonicalEffectiveMotive composition scheme :=
  rfl

/-- Morphism formula for the parent Boundary effective motive functor. -/
theorem TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor_map
    {source target : Geometry.SmSchemeOver k}
    (morphism : source ⟶ target) :
    (TraceAnalyticEffectiveRealization.boundaryEffectiveMotiveFunctor
        (composition := composition) hgraph).map morphism =
      canonicalEffectiveMotiveMap composition morphism :=
  rfl

/-- Parent Boundary embedding of effective motives into `DMgm`. -/
def TraceAnalyticEffectiveRealization.boundaryDMgmEmbedding :
    canonicalEffectiveMotives composition ⥤
      Boundary.VoevodskyDMgmQ_Q (composition := composition) :=
  Boundary.VoevodskyDMgmEffectiveEmbedding (composition := composition)

/-- The Boundary `DMgm` embedding is the parent effective embedding. -/
theorem TraceAnalyticEffectiveRealization.boundaryDMgmEmbedding_eq_parent :
    TraceAnalyticEffectiveRealization.boundaryDMgmEmbedding
        (composition := composition) =
      Boundary.VoevodskyDMgmEffectiveEmbedding (composition := composition) :=
  rfl

/-- Object formula for the parent Boundary `DMgm` effective embedding. -/
theorem TraceAnalyticEffectiveRealization.boundaryDMgmEmbedding_obj_effectiveObj
    (object : canonicalEffectiveMotives composition) :
    ((TraceAnalyticEffectiveRealization.boundaryDMgmEmbedding
        (composition := composition)).obj object).effectiveObj =
      object :=
  rfl

/-- Tate-degree formula for the parent Boundary `DMgm` effective embedding. -/
theorem TraceAnalyticEffectiveRealization.boundaryDMgmEmbedding_obj_tateTwist
    (object : canonicalEffectiveMotives composition) :
    ((TraceAnalyticEffectiveRealization.boundaryDMgmEmbedding
        (composition := composition)).obj object).tateTwist =
      0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
