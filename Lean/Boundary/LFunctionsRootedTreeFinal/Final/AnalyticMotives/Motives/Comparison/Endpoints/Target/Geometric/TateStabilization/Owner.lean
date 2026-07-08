import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.TateStabilization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Target.Geometric.Formulas.Owner

/-!
# Endpoint Tate-stabilization formulas for the geometric Boundary DMgm target

This file exposes the formal Tate-stabilization universal property of the
geometric Boundary `DMgm` target at analytic comparison endpoint names.  These
formulas control functors out of the geometric target by effective geometric
data plus Tate-shift compatibility.
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

/-- Endpoint geometric Tate-stabilization universal property. -/
abbrev TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationUniversalProperty
    (D : Type (u + 2)) [Category D] :=
  TraceAnalyticDMgmComparisonTarget.Geometric.tateStabilizationUniversalProperty
    (composition := composition) twistData D

/-- Endpoint geometric universal property is the Boundary geometric formal
Tate-stabilization universal property. -/
theorem TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationUniversalProperty_eq_boundary
    (D : Type (u + 2)) [Category D] :
    TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationUniversalProperty
        (composition := composition) twistData D =
      Boundary.boundaryGeometricMotivesTateStabilizationUniversalProperty
        (composition := composition) twistData D :=
  TraceAnalyticDMgmComparisonTarget.Geometric.tateStabilizationUniversalProperty_eq_boundary
    (composition := composition)
    twistData
    D

/-- Endpoint geometric universal property is the formal stabilization
universal property of the restricted geometric Tate action. -/
theorem TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationUniversalProperty_eq_formal
    (D : Type (u + 2)) [Category D] :
    TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationUniversalProperty
        (composition := composition) twistData D =
      Boundary.Motives.tateStabilizationUniversalProperty
        (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)
        D :=
  TraceAnalyticDMgmComparisonTarget.Geometric.tateStabilizationUniversalProperty_eq_formal
    (composition := composition)
    twistData
    D

/-- Endpoint geometric Tate-stabilization extension data. -/
abbrev TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension
    (D : Type (u + 2)) [Category D] :=
  TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension
    (composition := composition) twistData D

/-- Endpoint geometric extension data is the Boundary formal extension data for
the restricted geometric Tate action. -/
theorem TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension_eq_boundary
    (D : Type (u + 2)) [Category D] :
    TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension
        (composition := composition) twistData D =
      Boundary.Motives.TateStabilizationExtension
        (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)
        D :=
  TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_eq_boundary
    (composition := composition)
    twistData
    D

/-- Endpoint lift from geometric Tate-stabilization extension data. -/
def TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension.lift
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension
        (composition := composition) twistData D) :
    TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData ⥤ D :=
  TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension.lift
    (composition := composition)
    twistData
    extension

/-- Endpoint geometric lift is the target owner lift. -/
theorem TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension_lift_eq_target
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension
        (composition := composition) twistData D) :
    TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension.lift
        (composition := composition) twistData extension =
      TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension.lift
        (composition := composition) twistData extension :=
  rfl

/-- Endpoint object formula for a lifted geometric Tate-stabilization
extension. -/
theorem TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension_lift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension
        (composition := composition) twistData D)
    (object :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData) :
    (TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension.lift
      (composition := composition) twistData extension).obj object =
      extension.obj object.effectiveObj object.tateTwist :=
  TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_obj
    (composition := composition)
    twistData
    extension
    object

/-- Endpoint morphism formula for a lifted geometric Tate-stabilization
extension. -/
theorem TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension_lift_map
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension
        (composition := composition) twistData D)
    {source target :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension.lift
      (composition := composition) twistData extension).map hom =
      extension.map hom source.tateTwist target.tateTwist :=
  TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_map
    (composition := composition)
    twistData
    extension
    hom

/-- Endpoint formula for the lifted geometric extension after geometric
effective embedding. -/
theorem TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension_lift_effectiveEmbedding_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension
        (composition := composition) twistData D)
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    ((TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
        (composition := composition) twistData) ⋙
      TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension.lift
        (composition := composition) twistData extension).obj object =
      extension.obj object 0 :=
  TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_effectiveEmbedding_obj
    (composition := composition)
    twistData
    extension
    object

/-- Endpoint formula for lifted geometric extension maps after geometric
effective embedding. -/
theorem TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension_lift_effectiveEmbedding_map
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension
        (composition := composition) twistData D)
    {source target :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)}
    (hom : source ⟶ target) :
    ((TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
        (composition := composition) twistData) ⋙
      TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension.lift
        (composition := composition) twistData extension).map hom =
      extension.map hom 0 0 :=
  TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_effectiveEmbedding_map
    (composition := composition)
    twistData
    extension
    hom

/-- Endpoint formula for the lifted geometric extension after geometric Tate
shift. -/
theorem TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension_lift_tateShift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension
        (composition := composition) twistData D)
    (object :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData) :
    (TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension.lift
      (composition := composition) twistData extension).obj
        ((Boundary.Motives.tateShift
          (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
            (composition := composition) twistData)).obj object) =
      extension.obj object.effectiveObj (object.tateTwist + 1) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_tateShift_obj
    (composition := composition)
    twistData
    extension
    object

/-- Endpoint formula for the lifted geometric extension after inverse geometric
Tate shift. -/
theorem TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension_lift_inverseTateShift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension
        (composition := composition) twistData D)
    (object :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData) :
    (TraceAnalyticMotiveComparison.GeometricTargetTateStabilizationExtension.lift
      (composition := composition) twistData extension).obj
        ((Boundary.Motives.inverseTateShift
          (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
            (composition := composition) twistData)).obj object) =
      extension.obj object.effectiveObj (object.tateTwist - 1) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_inverseTateShift_obj
    (composition := composition)
    twistData
    extension
    object

end AnalyticMotives
end LFunctions
end Boundary
