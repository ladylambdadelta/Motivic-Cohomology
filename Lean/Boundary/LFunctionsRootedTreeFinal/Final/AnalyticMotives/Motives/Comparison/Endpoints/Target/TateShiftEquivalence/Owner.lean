import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.TateShiftEquivalence.Owner

/-!
# Endpoint Tate-shift equivalence components for the Boundary DMgm target

This file exposes the functor, inverse, and unit/counit components of the
concrete parent Boundary `DMgm` Tate-shift equivalence at analytic comparison
endpoint names.
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

/-- Endpoint formula: the concrete target Tate-shift equivalence functor is
formal Tate shift. -/
theorem TraceAnalyticMotiveComparison.targetTateShiftEquivalence_functor_eq :
    (TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
      (composition := composition)).functor =
      Boundary.Motives.tateShift
        (boundaryEffectiveTateObject (composition := composition)) :=
  TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_functor_eq
    (composition := composition)

/-- Endpoint formula: the concrete target Tate-shift equivalence inverse is
formal inverse Tate shift. -/
theorem TraceAnalyticMotiveComparison.targetTateShiftEquivalence_inverse_eq :
    (TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
      (composition := composition)).inverse =
      Boundary.Motives.inverseTateShift
        (boundaryEffectiveTateObject (composition := composition)) :=
  TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_inverse_eq
    (composition := composition)

/-- Endpoint formula: the concrete target Tate-shift unit component is the
identity on the underlying effective motive. -/
theorem TraceAnalyticMotiveComparison.targetTateShiftEquivalence_unit_hom_app
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
      (composition := composition)).unitIso.hom.app object =
      𝟙 object.effectiveObj :=
  TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_unit_hom_app
    (composition := composition)
    object

/-- Endpoint formula: the inverse concrete target Tate-shift unit component is
the identity on the underlying effective motive. -/
theorem TraceAnalyticMotiveComparison.targetTateShiftEquivalence_unit_inv_app
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
      (composition := composition)).unitIso.inv.app object =
      𝟙 object.effectiveObj :=
  TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_unit_inv_app
    (composition := composition)
    object

/-- Endpoint formula: the concrete target Tate-shift counit component is the
identity on the underlying effective motive. -/
theorem TraceAnalyticMotiveComparison.targetTateShiftEquivalence_counit_hom_app
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
      (composition := composition)).counitIso.hom.app object =
      𝟙 object.effectiveObj :=
  TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_counit_hom_app
    (composition := composition)
    object

/-- Endpoint formula: the inverse concrete target Tate-shift counit component
is the identity on the underlying effective motive. -/
theorem TraceAnalyticMotiveComparison.targetTateShiftEquivalence_counit_inv_app
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence
      (composition := composition)).counitIso.inv.app object =
      𝟙 object.effectiveObj :=
  TraceAnalyticDMgmComparisonTarget.tateShiftEquivalence_counit_inv_app
    (composition := composition)
    object

end AnalyticMotives
end LFunctions
end Boundary
