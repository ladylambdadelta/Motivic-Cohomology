import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Owner

/-!
# Geometric Tate-shift equivalence formulas for analytic comparison

This file exposes the functor, inverse functor, and identity unit/counit
components of the formal Tate-shift equivalence on the geometric Boundary
motive target.
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

variable (twistData :
  TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
    (composition := composition))

/-- The functor of the geometric Tate-shift equivalence is the formal Tate
shift functor. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_functor_eq :
    (TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence
      (composition := composition) twistData).functor =
      Boundary.Motives.tateShift
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData) :=
  rfl

/-- The inverse functor of the geometric Tate-shift equivalence is the inverse
formal Tate shift functor. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_inverse_eq :
    (TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence
      (composition := composition) twistData).inverse =
      Boundary.Motives.inverseTateShift
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData) :=
  rfl

/-- The unit component of the geometric Tate-shift equivalence is the identity
morphism on the underlying effective geometric motive. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_unit_hom_app
    (object :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) :
    (TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence
      (composition := composition) twistData).unitIso.hom.app object =
      𝟙 object.effectiveObj :=
  rfl

/-- The inverse unit component of the geometric Tate-shift equivalence is the
identity morphism on the underlying effective geometric motive. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_unit_inv_app
    (object :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) :
    (TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence
      (composition := composition) twistData).unitIso.inv.app object =
      𝟙 object.effectiveObj :=
  rfl

/-- The counit component of the geometric Tate-shift equivalence is the
identity morphism on the underlying effective geometric motive. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_counit_hom_app
    (object :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) :
    (TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence
      (composition := composition) twistData).counitIso.hom.app object =
      𝟙 object.effectiveObj :=
  rfl

/-- The inverse counit component of the geometric Tate-shift equivalence is the
identity morphism on the underlying effective geometric motive. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_counit_inv_app
    (object :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) :
    (TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence
      (composition := composition) twistData).counitIso.inv.app object =
      𝟙 object.effectiveObj :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
