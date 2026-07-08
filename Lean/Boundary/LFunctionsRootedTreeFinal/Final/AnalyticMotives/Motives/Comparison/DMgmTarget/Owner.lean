import Boundary.DMgm
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Owner

/-!
# Concrete Boundary DMgm target for analytic comparison

This file names the actual Boundary-side `DM_gm(Q)_Q` target used by the
analytic-motives comparison lane.  The analytic source is the Verdier-localized
stable analytic motive category; the target is the existing Boundary
construction `VoevodskyDMgmQ_Q`.
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

/-- The analytic source category for the comparison is the stable analytic Verdier quotient. -/
abbrev TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticStableMotiveCategory

/-- The comparison source is the stable analytic motive category. -/
theorem TraceAnalyticDMgmComparisonSource_eq_stable :
    TraceAnalyticDMgmComparisonSource =
      TraceAnalyticStableMotiveCategory :=
  rfl

/-- The analytic comparison source has integer shifts. -/
def TraceAnalyticDMgmComparisonSource.hasShiftStructure :
    HasShift TraceAnalyticDMgmComparisonSource ℤ :=
  TraceAnalyticStableMotiveCategory.hasShiftStructure

/-- The analytic comparison source is pretriangulated. -/
def TraceAnalyticDMgmComparisonSource.pretriangulatedStructure :
    Pretriangulated TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticStableMotiveCategory.pretriangulatedStructure

/-- The analytic comparison source is triangulated. -/
def TraceAnalyticDMgmComparisonSource.triangulatedStructure :
    IsTriangulated TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticStableMotiveCategory.triangulatedStructure

/-- Distinguished triangles in the analytic comparison source. -/
def TraceAnalyticDMgmComparisonSource.distinguishedTriangles :
    Set (Pretriangulated.Triangle TraceAnalyticDMgmComparisonSource) :=
  TraceAnalyticStableMotiveCategory.distinguishedTriangles

/-- Source distinguished triangles are the stable analytic distinguished triangles. -/
theorem TraceAnalyticDMgmComparisonSource.distinguishedTriangles_eq_stable :
    TraceAnalyticDMgmComparisonSource.distinguishedTriangles =
      TraceAnalyticStableMotiveCategory.distinguishedTriangles :=
  rfl

/-- The concrete Boundary `DM_gm(Q)_Q` target for the analytic comparison. -/
abbrev TraceAnalyticDMgmComparisonTarget :=
  Boundary.VoevodskyDMgmQ_Q (composition := composition)

/-- The comparison target is the Boundary `VoevodskyDMgmQ_Q` construction. -/
theorem TraceAnalyticDMgmComparisonTarget_eq_boundary :
    TraceAnalyticDMgmComparisonTarget (composition := composition) =
      Boundary.VoevodskyDMgmQ_Q (composition := composition) :=
  rfl

/-- The degree-zero effective embedding into the concrete Boundary DMgm target. -/
def TraceAnalyticDMgmComparisonTarget.effectiveEmbedding :
    canonicalEffectiveMotives composition ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  Boundary.VoevodskyDMgmEffectiveEmbedding (composition := composition)

/-- The comparison-target effective embedding is the Boundary effective embedding. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveEmbedding_eq_boundary :
    TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition) =
      Boundary.VoevodskyDMgmEffectiveEmbedding (composition := composition) :=
  rfl

/-- Effective objects enter the comparison target with their original effective object. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveEmbedding_obj_effectiveObj
    (object : canonicalEffectiveMotives composition) :
    ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition)).obj object).effectiveObj =
      object :=
  rfl

/-- Effective objects enter the comparison target in Tate degree zero. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveEmbedding_obj_tateTwist
    (object : canonicalEffectiveMotives composition) :
    ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition)).obj object).tateTwist =
      0 :=
  rfl

/-- The Tate-shift equivalence on the concrete Boundary DMgm target. -/
def TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence :
    TraceAnalyticDMgmComparisonTarget (composition := composition) ≌
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  Boundary.VoevodskyDMgmTateShiftEquivalence (composition := composition)

/-- The comparison-target Tate shift is the Boundary Tate-shift equivalence. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_eq_boundary :
    TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
        (composition := composition) =
      Boundary.VoevodskyDMgmTateShiftEquivalence (composition := composition) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
