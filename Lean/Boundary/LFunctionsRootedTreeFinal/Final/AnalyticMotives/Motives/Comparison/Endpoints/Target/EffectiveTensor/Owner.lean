import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.EffectiveTensor.Owner

/-!
# Endpoint effective tensor geometry for the Boundary DMgm target

This file exposes the effective geometric and tensor data of the parent
Boundary `DMgm` target at the analytic comparison endpoint.  The formulas are
the target-side tensor geometry that a later analytic-to-`DMgm` comparison must
respect on effective generators.
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

/-- Endpoint effective geometric motives are the parent Boundary effective
geometric motives. -/
abbrev TraceAnalyticMotiveComparison.targetEffectiveGeometricMotives :=
  TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
    (composition := composition)

/-- Endpoint effective geometric motives are the canonical Boundary geometric
effective motives. -/
theorem TraceAnalyticMotiveComparison.targetEffectiveGeometricMotives_eq_canonical :
    TraceAnalyticMotiveComparison.targetEffectiveGeometricMotives
        (composition := composition) =
      canonicalGeometricEffectiveMotives composition :=
  TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives_eq_canonical
    (composition := composition)

/-- Endpoint effective tensor geometry of the parent Boundary DMgm target. -/
abbrev TraceAnalyticMotiveComparison.targetEffectiveTensorGeometry
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition) :=
  TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry
    (composition := composition) hgraph

/-- Endpoint effective tensor geometry is the canonical Boundary tensor
geometry on effective motives. -/
theorem TraceAnalyticMotiveComparison.targetEffectiveTensorGeometry_eq_canonical
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition) :
    TraceAnalyticMotiveComparison.targetEffectiveTensorGeometry
        (composition := composition) hgraph =
      canonicalEffectiveMotives_tensorGeometry
        (composition := composition) hgraph :=
  TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry_eq_canonical
    (composition := composition)
    hgraph

/-- Endpoint tensor-object formula for smooth effective generators. -/
theorem TraceAnalyticMotiveComparison.targetEffectiveTensorGeometry_tensor_obj
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (source target : Geometry.SmSchemeOver k) :
    (TraceAnalyticMotiveComparison.targetEffectiveTensorGeometry
      (composition := composition) hgraph).tensor.obj (source, target) =
      canonicalEffectiveMotiveExternalProduct composition source target :=
  TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry_tensor_obj
    (composition := composition)
    hgraph
    source
    target

/-- Endpoint associator formula for the target effective tensor geometry. -/
theorem TraceAnalyticMotiveComparison.targetEffectiveTensorGeometry_assoc
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (first second third : Geometry.SmSchemeOver k) :
    (TraceAnalyticMotiveComparison.targetEffectiveTensorGeometry
      (composition := composition) hgraph).assoc first second third =
      canonicalEffectiveMotives_tensor_assoc
        composition hgraph first second third :=
  TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry_assoc
    (composition := composition)
    hgraph
    first
    second
    third

/-- Endpoint left-unitor formula for the target effective tensor geometry. -/
theorem TraceAnalyticMotiveComparison.targetEffectiveTensorGeometry_leftUnitor
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (object : Geometry.SmSchemeOver k) :
    (TraceAnalyticMotiveComparison.targetEffectiveTensorGeometry
      (composition := composition) hgraph).leftUnitor object =
      canonicalEffectiveMotives_tensor_leftUnitor composition hgraph object :=
  TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry_leftUnitor
    (composition := composition)
    hgraph
    object

/-- Endpoint right-unitor formula for the target effective tensor geometry. -/
theorem TraceAnalyticMotiveComparison.targetEffectiveTensorGeometry_rightUnitor
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (object : Geometry.SmSchemeOver k) :
    (TraceAnalyticMotiveComparison.targetEffectiveTensorGeometry
      (composition := composition) hgraph).rightUnitor object =
      canonicalEffectiveMotives_tensor_rightUnitor composition hgraph object :=
  TraceAnalyticDMgmComparisonTarget.effectiveTensorGeometry_rightUnitor
    (composition := composition)
    hgraph
    object

/-- Endpoint Tate-stability of the effective geometric subcategory. -/
theorem TraceAnalyticMotiveComparison.targetEffectiveGeometric_tateTwist_stable
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (object :
      TraceAnalyticMotiveComparison.targetEffectiveGeometricMotives
        (composition := composition)) :
    (canonicalGeometricEffectiveThickSubcategory composition).P
      (twistData.functor.obj object.1) :=
  TraceAnalyticDMgmComparisonTarget.effectiveGeometric_tateTwist_stable
    (composition := composition)
    twistData
    object

end AnalyticMotives
end LFunctions
end Boundary
