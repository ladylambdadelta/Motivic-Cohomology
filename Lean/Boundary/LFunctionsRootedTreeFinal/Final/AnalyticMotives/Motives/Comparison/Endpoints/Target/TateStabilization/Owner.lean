import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.TateStabilization.Owner

/-!
# Endpoint Tate-stabilization formulas for the Boundary DMgm target

This file records the comparison-endpoint form of the parent Boundary `DMgm`
Tate-stabilization universal property.  These are the target-side formulas used
when a later comparison functor is checked against effective motives and Tate
shift.
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

/-- Endpoint form of the Boundary Tate-stabilization universal property carried
by the concrete comparison target. -/
def TraceAnalyticMotiveComparison.targetTateStabilizationUniversalProperty :
    Boundary.VoevodskyDMgmTateStabilizationUniversalProperty
      (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget.tateStabilizationUniversalProperty
    (composition := composition)

/-- The endpoint Tate-stabilization universal property is the concrete target
owner package. -/
theorem TraceAnalyticMotiveComparison.targetTateStabilizationUniversalProperty_eq_target :
    TraceAnalyticMotiveComparison.targetTateStabilizationUniversalProperty
        (composition := composition) =
      TraceAnalyticDMgmComparisonTarget.tateStabilizationUniversalProperty
        (composition := composition) :=
  rfl

/-- The endpoint Tate-stabilization universal property is the parent Boundary
canonical package. -/
theorem TraceAnalyticMotiveComparison.targetTateStabilizationUniversalProperty_eq_parent :
    TraceAnalyticMotiveComparison.targetTateStabilizationUniversalProperty
        (composition := composition) =
      Boundary.VoevodskyDMgmTateStabilizationUniversalProperty.canonical
        (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget.tateStabilizationUniversalProperty_eq_boundary
    (composition := composition)

/-- Endpoint form of the target Tate-stabilization extension data type. -/
abbrev TraceAnalyticMotiveComparison.TargetTateStabilizationExtension
    (D : Type (u + 2)) [Category D] :=
  TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
    (composition := composition) D

/-- The endpoint target extension-data type is the parent Boundary extension
data type. -/
theorem TraceAnalyticMotiveComparison.TargetTateStabilizationExtension_eq_parent
    (D : Type (u + 2)) [Category D] :
    TraceAnalyticMotiveComparison.TargetTateStabilizationExtension
        (composition := composition) D =
      Boundary.VoevodskyDMgmTateStabilizationExtension
        (composition := composition) D :=
  TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_eq_boundary
    (composition := composition)
    D

/-- Endpoint lift out of the concrete Boundary DMgm comparison target from
Tate-stabilization extension data. -/
def TraceAnalyticMotiveComparison.TargetTateStabilizationExtension.lift
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.TargetTateStabilizationExtension
        (composition := composition) D) :
    TraceAnalyticDMgmComparisonTarget (composition := composition) ⥤ D :=
  TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension.lift
    (composition := composition)
    extension

/-- The endpoint lift is the target owner lift. -/
theorem TraceAnalyticMotiveComparison.TargetTateStabilizationExtension_lift_eq_target
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.TargetTateStabilizationExtension
        (composition := composition) D) :
    TraceAnalyticMotiveComparison.TargetTateStabilizationExtension.lift
        (composition := composition) extension =
      TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension.lift
        (composition := composition) extension :=
  rfl

/-- Endpoint object formula for a lifted target Tate-stabilization extension. -/
theorem TraceAnalyticMotiveComparison.TargetTateStabilizationExtension_lift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.TargetTateStabilizationExtension
        (composition := composition) D)
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticMotiveComparison.TargetTateStabilizationExtension.lift
      (composition := composition) extension).obj object =
      extension.obj object.effectiveObj object.tateTwist :=
  TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_lift_obj
    (composition := composition)
    extension
    object

/-- Endpoint morphism formula for a lifted target Tate-stabilization extension. -/
theorem TraceAnalyticMotiveComparison.TargetTateStabilizationExtension_lift_map
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.TargetTateStabilizationExtension
        (composition := composition) D)
    {source targetObject :
      TraceAnalyticDMgmComparisonTarget (composition := composition)}
    (hom : source ⟶ targetObject) :
    (TraceAnalyticMotiveComparison.TargetTateStabilizationExtension.lift
      (composition := composition) extension).map hom =
      extension.map hom source.tateTwist targetObject.tateTwist :=
  TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_lift_map
    (composition := composition)
    extension
    hom

/-- Endpoint formula for the lift after the effective embedding. -/
theorem TraceAnalyticMotiveComparison.TargetTateStabilizationExtension_lift_effectiveEmbedding_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.TargetTateStabilizationExtension
        (composition := composition) D)
    (object : canonicalEffectiveMotives composition) :
    ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition)) ⋙
      TraceAnalyticMotiveComparison.TargetTateStabilizationExtension.lift
        (composition := composition) extension).obj object =
      extension.obj object 0 :=
  TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_lift_effectiveEmbedding_obj
    (composition := composition)
    extension
    object

/-- Endpoint formula for the lifted target extension after the formal Tate
shift. -/
theorem TraceAnalyticMotiveComparison.TargetTateStabilizationExtension_lift_tateShift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.TargetTateStabilizationExtension
        (composition := composition) D)
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticMotiveComparison.TargetTateStabilizationExtension.lift
      (composition := composition) extension).obj
        ((Boundary.Motives.tateShift
          (boundaryEffectiveTateObject (composition := composition))).obj object) =
      extension.obj object.effectiveObj (object.tateTwist + 1) :=
  TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_lift_tateShift_obj
    (composition := composition)
    extension
    object

/-- Endpoint formula for the lifted target extension after inverse formal Tate
shift. -/
theorem TraceAnalyticMotiveComparison.TargetTateStabilizationExtension_lift_inverseTateShift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticMotiveComparison.TargetTateStabilizationExtension
        (composition := composition) D)
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticMotiveComparison.TargetTateStabilizationExtension.lift
      (composition := composition) extension).obj
        ((Boundary.Motives.inverseTateShift
          (boundaryEffectiveTateObject (composition := composition))).obj object) =
      extension.obj object.effectiveObj (object.tateTwist - 1) :=
  TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_lift_inverseTateShift_obj
    (composition := composition)
    extension
    object

end AnalyticMotives
end LFunctions
end Boundary
