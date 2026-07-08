import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Owner

/-!
# Boundary effective tensor geometry for analytic DMgm comparison

This file exposes the Boundary effective-motive tensor geometry used by the
concrete `DM_gm(Q)_Q` target under analytic comparison target names.
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

/-- Effective geometric motives entering the analytic comparison target. -/
abbrev TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives :=
  Boundary.VoevodskyDMgmEffectiveGeometricQ_Q (composition := composition)

/-- The analytic comparison target's effective geometric motives are the
canonical Boundary geometric effective motives. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives_eq_canonical :
    TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition) =
      canonicalGeometricEffectiveMotives composition :=
  Boundary.VoevodskyDMgmEffectiveGeometricQ_Q_eq_canonical
    (composition := composition)

/-- Effective tensor geometry entering the analytic comparison target. -/
abbrev TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition) :=
  Boundary.VoevodskyDMgmEffectiveTensorGeometry
    (composition := composition) hgraph

/-- The analytic comparison target's effective tensor geometry is the canonical
Boundary effective-motive tensor geometry. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry_eq_canonical
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition) :
    TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry
        (composition := composition) hgraph =
      canonicalEffectiveMotives_tensorGeometry
        (composition := composition) hgraph :=
  Boundary.VoevodskyDMgmEffectiveTensorGeometry_eq_canonical
    (composition := composition) hgraph

/-- Tensor objects in the analytic comparison target's effective tensor
geometry are canonical external products of smooth schemes. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry_tensor_obj
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (source target : Geometry.SmSchemeOver k) :
    (TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry
      (composition := composition) hgraph).tensor.obj (source, target) =
      canonicalEffectiveMotiveExternalProduct composition source target :=
  Boundary.VoevodskyDMgmEffectiveTensorGeometry_tensor_obj
    (composition := composition) hgraph source target

/-- Associativity in the analytic comparison target's effective tensor geometry
is the canonical Boundary tensor associator. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry_assoc
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (first second third : Geometry.SmSchemeOver k) :
    (TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry
      (composition := composition) hgraph).assoc first second third =
      canonicalEffectiveMotives_tensor_assoc
        composition hgraph first second third :=
  Boundary.VoevodskyDMgmEffectiveTensorGeometry_assoc
    (composition := composition) hgraph first second third

/-- The left unitor in the analytic comparison target's effective tensor
geometry is the canonical Boundary left unitor. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry_leftUnitor
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (object : Geometry.SmSchemeOver k) :
    (TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry
      (composition := composition) hgraph).leftUnitor object =
      canonicalEffectiveMotives_tensor_leftUnitor composition hgraph object :=
  Boundary.VoevodskyDMgmEffectiveTensorGeometry_leftUnitor
    (composition := composition) hgraph object

/-- The right unitor in the analytic comparison target's effective tensor
geometry is the canonical Boundary right unitor. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry_rightUnitor
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (object : Geometry.SmSchemeOver k) :
    (TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry
      (composition := composition) hgraph).rightUnitor object =
      canonicalEffectiveMotives_tensor_rightUnitor composition hgraph object :=
  Boundary.VoevodskyDMgmEffectiveTensorGeometry_rightUnitor
    (composition := composition) hgraph object

/-- Boundary Tate-action functor constructions preserve the effective geometric
subcategory used by the analytic comparison target. -/
theorem TraceAnalyticDMgmComparisonTarget.effectiveGeometric_tateTwist_stable
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    (canonicalGeometricEffectiveThickSubcategory composition).P
      (twistData.functor.obj object.1) :=
  Boundary.VoevodskyDMgmEffectiveGeometric_tateTwist_stable
    (composition := composition) twistData object

end AnalyticMotives
end LFunctions
end Boundary
