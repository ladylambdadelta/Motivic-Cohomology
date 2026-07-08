import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Owner

/-!
# Tate-shift equivalence formulas for the Boundary DMgm comparison target

This file exposes the functor and inverse functor carried by the formal
Tate-shift equivalence on the concrete Boundary `DM_gm(Q)_Q` target.
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

/-- The functor of the comparison-target Tate-shift equivalence is the formal
Tate shift functor. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_functor_eq :
    (TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
      (composition := composition)).functor =
      Boundary.Motives.tateShift
        (boundaryEffectiveTateObject (composition := composition)) :=
  rfl

/-- The inverse functor of the comparison-target Tate-shift equivalence is the
inverse formal Tate shift functor. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_inverse_eq :
    (TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
      (composition := composition)).inverse =
      Boundary.Motives.inverseTateShift
        (boundaryEffectiveTateObject (composition := composition)) :=
  rfl

/-- The unit component of the comparison-target Tate-shift equivalence is the
identity morphism on the underlying effective motive. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_unit_hom_app
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
      (composition := composition)).unitIso.hom.app object =
      𝟙 object.effectiveObj :=
  rfl

/-- The inverse unit component of the comparison-target Tate-shift equivalence
is the identity morphism on the underlying effective motive. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_unit_inv_app
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
      (composition := composition)).unitIso.inv.app object =
      𝟙 object.effectiveObj :=
  rfl

/-- The counit component of the comparison-target Tate-shift equivalence is the
identity morphism on the underlying effective motive. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_counit_hom_app
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
      (composition := composition)).counitIso.hom.app object =
      𝟙 object.effectiveObj :=
  rfl

/-- The inverse counit component of the comparison-target Tate-shift equivalence
is the identity morphism on the underlying effective motive. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_counit_inv_app
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
      (composition := composition)).counitIso.inv.app object =
      𝟙 object.effectiveObj :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
