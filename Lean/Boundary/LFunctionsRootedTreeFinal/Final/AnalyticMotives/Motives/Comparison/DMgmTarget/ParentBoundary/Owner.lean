import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.TateStabilization.Owner

/-!
# Parent Boundary DMgm identifications for analytic comparison

This file records that the analytic comparison target is the parent Boundary
`DMgm` construction, not a parallel target.  The point is to expose the exact
owner equalities consumed by the later weight-triangular comparison.
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

/-- The analytic comparison target is the short parent Boundary `DMgm` alias. -/
theorem TraceAnalyticDMgmComparisonTarget_eq_parentDMgm :
    TraceAnalyticDMgmComparisonTarget (composition := composition) =
      Boundary.DMgmQ_Q (composition := composition) :=
  rfl

/-- The analytic comparison target is the Voevodsky-style Boundary `DMgm`
construction. -/
theorem TraceAnalyticDMgmComparisonTarget_eq_VoevodskyDMgm :
    TraceAnalyticDMgmComparisonTarget (composition := composition) =
      Boundary.VoevodskyDMgmQ_Q (composition := composition) :=
  rfl

/-- The analytic comparison target is the formal stabilization of canonical
effective motives at the projective-geometric Tate object. -/
theorem TraceAnalyticDMgmComparisonTarget_eq_projectiveGeometricTateStabilization :
    TraceAnalyticDMgmComparisonTarget (composition := composition) =
      Boundary.boundaryMotivesOfProjectiveGeometricTateObject
        (composition := composition) :=
  rfl

/-- The parent Boundary `DMgm` alias is the same target as the analytic
comparison target. -/
theorem parentDMgm_eq_TraceAnalyticDMgmComparisonTarget :
    Boundary.DMgmQ_Q (composition := composition) =
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  rfl

/-- The effective geometric input visible from the analytic comparison target is
the parent Boundary effective geometric motive category. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives_eq_parent :
    TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition) =
      Boundary.VoevodskyDMgmEffectiveGeometricQ_Q
        (composition := composition) :=
  rfl

/-- The effective embedding visible from the analytic comparison target is the
parent Boundary `DMgm` effective embedding. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveEmbedding_eq_parent :
    TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition) =
      Boundary.VoevodskyDMgmEffectiveEmbedding
        (composition := composition) :=
  rfl

/-- The Tate-shift equivalence visible from the analytic comparison target is
the parent Boundary `DMgm` Tate-shift equivalence. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_eq_parent :
    TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
        (composition := composition) =
      Boundary.VoevodskyDMgmTateShiftEquivalence
        (composition := composition) :=
  rfl

/-- The target universal-property package visible from the analytic comparison
target is the parent Boundary `DMgm` universal-property package. -/
theorem TraceAnalyticDMgmComparisonTarget.tateStabilizationUniversalProperty_eq_parent :
    TraceAnalyticDMgmComparisonTarget.tateStabilizationUniversalProperty
        (composition := composition) =
      Boundary.VoevodskyDMgmTateStabilizationUniversalProperty.canonical
        (composition := composition) :=
  rfl

/-- The target extension-data type visible from the analytic comparison target
is the parent Boundary `DMgm` extension-data type. -/
theorem TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_eq_parent
    (D : Type (u + 2)) [Category D] :
    TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
        (composition := composition) D =
      Boundary.VoevodskyDMgmTateStabilizationExtension
        (composition := composition) D :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
