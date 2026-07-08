import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.TateShiftEquivalence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Target.Geometric.Formulas.Owner

/-!
# Endpoint geometric Tate-shift equivalence components

This file exposes the functor, inverse, and unit/counit components of the
geometric Boundary `DMgm` Tate-shift equivalence at analytic comparison
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

variable (twistData :
  TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
    (composition := composition))

/-- Endpoint formula: the functor of the geometric Tate-shift equivalence is
formal Tate shift. -/
theorem TraceAnalyticMotiveComparison.geometricTateShiftEquivalence_functor_eq :
    (TraceAnalyticMotiveComparison.geometricTateShiftEquivalence
      (composition := composition) twistData).functor =
      Boundary.Motives.tateShift
        (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData) :=
  TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_functor_eq
    (composition := composition)
    twistData

/-- Endpoint formula: the inverse of the geometric Tate-shift equivalence is
formal inverse Tate shift. -/
theorem TraceAnalyticMotiveComparison.geometricTateShiftEquivalence_inverse_eq :
    (TraceAnalyticMotiveComparison.geometricTateShiftEquivalence
      (composition := composition) twistData).inverse =
      Boundary.Motives.inverseTateShift
        (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData) :=
  TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_inverse_eq
    (composition := composition)
    twistData

/-- Endpoint formula: the geometric Tate-shift unit component is the identity
on the underlying effective geometric motive. -/
theorem TraceAnalyticMotiveComparison.geometricTateShiftEquivalence_unit_hom_app
    (object :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData) :
    (TraceAnalyticMotiveComparison.geometricTateShiftEquivalence
      (composition := composition) twistData).unitIso.hom.app object =
      𝟙 object.effectiveObj :=
  TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_unit_hom_app
    (composition := composition)
    twistData
    object

/-- Endpoint formula: the inverse geometric Tate-shift unit component is the
identity on the underlying effective geometric motive. -/
theorem TraceAnalyticMotiveComparison.geometricTateShiftEquivalence_unit_inv_app
    (object :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData) :
    (TraceAnalyticMotiveComparison.geometricTateShiftEquivalence
      (composition := composition) twistData).unitIso.inv.app object =
      𝟙 object.effectiveObj :=
  TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_unit_inv_app
    (composition := composition)
    twistData
    object

/-- Endpoint formula: the geometric Tate-shift counit component is the identity
on the underlying effective geometric motive. -/
theorem TraceAnalyticMotiveComparison.geometricTateShiftEquivalence_counit_hom_app
    (object :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData) :
    (TraceAnalyticMotiveComparison.geometricTateShiftEquivalence
      (composition := composition) twistData).counitIso.hom.app object =
      𝟙 object.effectiveObj :=
  TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_counit_hom_app
    (composition := composition)
    twistData
    object

/-- Endpoint formula: the inverse geometric Tate-shift counit component is the
identity on the underlying effective geometric motive. -/
theorem TraceAnalyticMotiveComparison.geometricTateShiftEquivalence_counit_inv_app
    (object :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData) :
    (TraceAnalyticMotiveComparison.geometricTateShiftEquivalence
      (composition := composition) twistData).counitIso.inv.app object =
      𝟙 object.effectiveObj :=
  TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_counit_inv_app
    (composition := composition)
    twistData
    object

end AnalyticMotives
end LFunctions
end Boundary
