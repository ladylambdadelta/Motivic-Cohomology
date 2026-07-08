import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Owner

/-!
# Geometric DMgm Tate-stabilization formulas for analytic comparison

This file exposes the formal Tate-stabilization extension API for the
geometric Boundary motive target under analytic comparison names.
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

/-- Formal Tate-stabilization universal property for the analytic geometric
target. -/
abbrev TraceAnalyticDMgmComparisonTarget.Geometric.tateStabilizationUniversalProperty
    (D : Type (u + 2)) [Category D] :=
  Boundary.boundaryGeometricMotivesTateStabilizationUniversalProperty
    (composition := composition) twistData D

/-- The analytic geometric universal property is the Boundary geometric formal
Tate-stabilization universal property. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.tateStabilizationUniversalProperty_eq_boundary
    (D : Type (u + 2)) [Category D] :
    TraceAnalyticDMgmComparisonTarget.Geometric.tateStabilizationUniversalProperty
        (composition := composition) twistData D =
      Boundary.boundaryGeometricMotivesTateStabilizationUniversalProperty
        (composition := composition) twistData D :=
  rfl

/-- The analytic geometric universal property is the formal stabilization
universal property of the restricted geometric Tate-action functor. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.tateStabilizationUniversalProperty_eq_formal
    (D : Type (u + 2)) [Category D] :
    TraceAnalyticDMgmComparisonTarget.Geometric.tateStabilizationUniversalProperty
        (composition := composition) twistData D =
      Boundary.Motives.tateStabilizationUniversalProperty
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)
        D :=
  rfl

/-- Tate-stabilization extension data out of the analytic geometric target. -/
abbrev TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension
    (D : Type (u + 2)) [Category D] :=
  Boundary.Motives.TateStabilizationExtension
    (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
      (composition := composition) twistData)
    D

/-- The analytic geometric extension data is the Boundary formal
Tate-stabilization extension data for the restricted Tate-action functor. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_eq_boundary
    (D : Type (u + 2)) [Category D] :
    TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension
        (composition := composition) twistData D =
      Boundary.Motives.TateStabilizationExtension
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)
        D :=
  rfl

/-- Lift geometric Tate-stabilization extension data to a functor out of the
analytic geometric target. -/
def TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension.lift
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension
        (composition := composition) twistData D) :
    TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData ⥤ D :=
  Boundary.Motives.TateStabilizationExtension.lift extension

/-- The analytic geometric lift is the Boundary formal Tate-stabilization lift. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_eq_boundary
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension
        (composition := composition) twistData D) :
    TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension.lift
        (composition := composition) twistData extension =
      Boundary.Motives.TateStabilizationExtension.lift extension :=
  rfl

/-- Object formula for a lifted geometric Tate-stabilization extension. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension
        (composition := composition) twistData D)
    (object :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension.lift
      (composition := composition) twistData extension).obj object =
      extension.obj object.effectiveObj object.tateTwist :=
  rfl

/-- Morphism formula for a lifted geometric Tate-stabilization extension. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_map
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension
        (composition := composition) twistData D)
    {source target :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData}
    (hom : source ⟶ target) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension.lift
      (composition := composition) twistData extension).map hom =
      extension.map hom source.tateTwist target.tateTwist :=
  rfl

/-- Lifted geometric extension value on the geometric effective embedding. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_effectiveEmbedding_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension
        (composition := composition) twistData D)
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    ((TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding
        (composition := composition) twistData) ⋙
      TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension.lift
        (composition := composition) twistData extension).obj object =
      extension.obj object 0 :=
  rfl

/-- Lifted geometric extension value on maps from the geometric effective
embedding. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_effectiveEmbedding_map
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension
        (composition := composition) twistData D)
    {source target :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)}
    (hom : source ⟶ target) :
    ((TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding
        (composition := composition) twistData) ⋙
      TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension.lift
        (composition := composition) twistData extension).map hom =
      extension.map hom 0 0 :=
  Boundary.Motives.TateStabilizationExtension.lift_comp_effectiveEmbedding_map
    extension
    hom

/-- Lifted geometric extension value after the geometric Tate shift. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_tateShift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension
        (composition := composition) twistData D)
    (object :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension.lift
      (composition := composition) twistData extension).obj
        ((Boundary.Motives.tateShift
          (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
            (composition := composition) twistData)).obj object) =
      extension.obj object.effectiveObj (object.tateTwist + 1) :=
  Boundary.Motives.TateStabilizationExtension.lift_tateShift_obj
    extension
    object

/-- Lifted geometric extension value after the inverse geometric Tate shift. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension_lift_inverseTateShift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension
        (composition := composition) twistData D)
    (object :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.TateStabilizationExtension.lift
      (composition := composition) twistData extension).obj
        ((Boundary.Motives.inverseTateShift
          (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
            (composition := composition) twistData)).obj object) =
      extension.obj object.effectiveObj (object.tateTwist - 1) :=
  Boundary.Motives.TateStabilizationExtension.lift_inverseTateShift_obj
    extension
    object

end AnalyticMotives
end LFunctions
end Boundary
