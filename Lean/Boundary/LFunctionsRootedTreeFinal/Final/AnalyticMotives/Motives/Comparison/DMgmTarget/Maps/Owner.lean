import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Owner

/-!
# Morphism formulas for the Boundary DMgm comparison target

This file exposes the morphism-level formulas for the concrete Boundary
`DM_gm(Q)_Q` target used by the analytic comparison lane.
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

/-- The comparison-target effective embedding acts as the identity on effective
morphisms in the formal Tate-stabilized target. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveEmbedding_map
    {source target : canonicalEffectiveMotives composition}
    (hom : source ⟶ target) :
    (TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
      (composition := composition)).map hom =
      hom :=
  rfl

/-- The formal Tate shift acts as the identity on morphisms of the comparison
target. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShift_map
    {source target :
      TraceAnalyticDMgmComparisonTarget (composition := composition)}
    (hom : source ⟶ target) :
    (Boundary.Motives.tateShift
      (boundaryEffectiveTateObject (composition := composition))).map hom =
      hom :=
  rfl

/-- The inverse formal Tate shift acts as the identity on morphisms of the
comparison target. -/
theorem TraceAnalyticDMgmComparisonTarget.inverseTateShift_map
    {source target :
      TraceAnalyticDMgmComparisonTarget (composition := composition)}
    (hom : source ⟶ target) :
    (Boundary.Motives.inverseTateShift
      (boundaryEffectiveTateObject (composition := composition))).map hom =
      hom :=
  rfl

/-- Formal Tate shift sends an effective embedded morphism to the same
underlying effective morphism. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShift_effectiveEmbedding_map
    {source target : canonicalEffectiveMotives composition}
    (hom : source ⟶ target) :
    (Boundary.Motives.tateShift
      (boundaryEffectiveTateObject (composition := composition))).map
        ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
          (composition := composition)).map hom) =
      hom :=
  rfl

/-- Inverse formal Tate shift sends an effective embedded morphism to the same
underlying effective morphism. -/
theorem TraceAnalyticDMgmComparisonTarget.inverseTateShift_effectiveEmbedding_map
    {source target : canonicalEffectiveMotives composition}
    (hom : source ⟶ target) :
    (Boundary.Motives.inverseTateShift
      (boundaryEffectiveTateObject (composition := composition))).map
        ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
          (composition := composition)).map hom) =
      hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
