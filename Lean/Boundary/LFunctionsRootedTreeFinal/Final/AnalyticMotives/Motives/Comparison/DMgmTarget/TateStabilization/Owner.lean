import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Owner

/-!
# Boundary DMgm Tate-stabilization surface for analytic comparison

This file exposes the already constructed Boundary formal Tate-stabilization
universal property under the analytic comparison target names.
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

/-- DMgm-facing Tate-stabilization extension data, exposed for the analytic
comparison target. -/
abbrev TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
    (D : Type (u + 2)) [Category D] :=
  Boundary.VoevodskyDMgmTateStabilizationExtension
    (composition := composition) D

/-- The analytic comparison target's extension data is the Boundary
Tate-stabilization extension data. -/
theorem TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_eq_boundary
    (D : Type (u + 2)) [Category D] :
    TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
        (composition := composition) D =
      Boundary.VoevodskyDMgmTateStabilizationExtension
        (composition := composition) D :=
  rfl

/-- Lift a Tate-stabilization extension out of the concrete Boundary DMgm
comparison target. -/
def TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension.lift
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
        (composition := composition) D) :
    TraceAnalyticDMgmComparisonTarget (composition := composition) ⥤ D :=
  Boundary.VoevodskyDMgmTateStabilizationExtension.lift
    (composition := composition) extension

/-- The analytic target lift is the Boundary Tate-stabilization lift. -/
theorem TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_lift_eq_boundary
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
        (composition := composition) D) :
    TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension.lift
        (composition := composition) extension =
      Boundary.VoevodskyDMgmTateStabilizationExtension.lift
        (composition := composition) extension :=
  rfl

/-- Object formula for a lifted Tate-stabilization extension out of the
analytic comparison target. -/
theorem TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_lift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
        (composition := composition) D)
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension.lift
      (composition := composition) extension).obj object =
      extension.obj object.effectiveObj object.tateTwist :=
  Boundary.VoevodskyDMgmTateStabilizationExtension_lift_obj
    (composition := composition)
    extension
    object

/-- Morphism formula for a lifted Tate-stabilization extension out of the
analytic comparison target. -/
theorem TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_lift_map
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
        (composition := composition) D)
    {source targetObject :
      TraceAnalyticDMgmComparisonTarget (composition := composition)}
    (hom : source ⟶ targetObject) :
    (TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension.lift
      (composition := composition) extension).map hom =
      extension.map hom source.tateTwist targetObject.tateTwist :=
  Boundary.VoevodskyDMgmTateStabilizationExtension_lift_map
    (composition := composition)
    extension
    hom

/-- Lifted extension value on the effective embedding in the analytic
comparison target. -/
theorem TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_lift_effectiveEmbedding_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
        (composition := composition) D)
    (object : canonicalEffectiveMotives composition) :
    ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition)) ⋙
      TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension.lift
        (composition := composition) extension).obj object =
      extension.obj object 0 :=
  Boundary.VoevodskyDMgmTateStabilizationExtension_lift_effectiveEmbedding_obj
    (composition := composition)
    extension
    object

/-- Lifted extension value on maps from the effective embedding in the analytic
comparison target. -/
theorem TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_lift_effectiveEmbedding_map
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
        (composition := composition) D)
    {source target : canonicalEffectiveMotives composition}
    (hom : source ⟶ target) :
    ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition)) ⋙
      TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension.lift
        (composition := composition) extension).map hom =
      extension.map hom 0 0 :=
  Boundary.Motives.TateStabilizationExtension.lift_comp_effectiveEmbedding_map
    extension
    hom

/-- Lifted extension value after the formal Tate shift in the analytic
comparison target. -/
theorem TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_lift_tateShift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
        (composition := composition) D)
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension.lift
      (composition := composition) extension).obj
        ((Boundary.Motives.tateShift
          (boundaryEffectiveTateObject (composition := composition))).obj object) =
      extension.obj object.effectiveObj (object.tateTwist + 1) :=
  Boundary.VoevodskyDMgmTateStabilizationExtension_lift_tateShift_obj
    (composition := composition)
    extension
    object

/-- Lifted extension value after the inverse formal Tate shift in the analytic
comparison target. -/
theorem TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension_lift_inverseTateShift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension
        (composition := composition) D)
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (TraceAnalyticDMgmComparisonTarget.TateStabilizationExtension.lift
      (composition := composition) extension).obj
        ((Boundary.Motives.inverseTateShift
          (boundaryEffectiveTateObject (composition := composition))).obj object) =
      extension.obj object.effectiveObj (object.tateTwist - 1) :=
  Boundary.Motives.TateStabilizationExtension.lift_inverseTateShift_obj
    extension
    object

/-- Canonical Tate-stabilization universal property of the concrete Boundary
DMgm target, exposed in the analytic comparison lane. -/
def TraceAnalyticDMgmComparisonTarget.tateStabilizationUniversalProperty :
    Boundary.VoevodskyDMgmTateStabilizationUniversalProperty
      (composition := composition) :=
  Boundary.VoevodskyDMgmTateStabilizationUniversalProperty.canonical
    (composition := composition)

/-- The analytic comparison target universal-property package is the Boundary
canonical package. -/
theorem TraceAnalyticDMgmComparisonTarget.tateStabilizationUniversalProperty_eq_boundary :
    TraceAnalyticDMgmComparisonTarget.tateStabilizationUniversalProperty
        (composition := composition) =
      Boundary.VoevodskyDMgmTateStabilizationUniversalProperty.canonical
        (composition := composition) :=
  rfl

/-- The analytic comparison target consumes the Boundary reduced-projective-line
Tate geometry theorem. -/
theorem TraceAnalyticDMgmComparisonTarget.tateObject_projectiveGeometry :
    (TraceAnalyticDMgmComparisonTarget.tateStabilizationUniversalProperty
      (composition := composition)).tateObject_projectiveGeometry =
      boundaryEffectiveTateObject_projectiveGeometry (composition := composition) :=
  Boundary.VoevodskyDMgmTateStabilizationUniversalProperty_projectiveGeometry
    (composition := composition)

/-- The analytic comparison target consumes the Boundary shifted-Tate
identification with the reduced projective line. -/
theorem TraceAnalyticDMgmComparisonTarget.tateObject_shifted_iso :
    (TraceAnalyticDMgmComparisonTarget.tateStabilizationUniversalProperty
      (composition := composition)).tateObject_shifted_iso_reducedProjectiveLine =
      boundaryEffectiveTateObject_shifted_iso_reducedProjectiveLine
        (composition := composition) :=
  Boundary.VoevodskyDMgmTateStabilizationUniversalProperty_tateObject_shifted_iso
    (composition := composition)

/-- The formal Tate shift sends the embedded effective Tate object to Tate
degree one in the analytic comparison target. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShift_effectiveEmbedding_tateObject :
    (Boundary.Motives.tateShift
        (boundaryEffectiveTateObject (composition := composition))).obj
      ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
          (composition := composition)).obj
        (boundaryEffectiveTateObject (composition := composition))) =
      ⟨boundaryEffectiveTateObject (composition := composition), 1⟩ :=
  Boundary.VoevodskyDMgmTateShift_effectiveEmbedding_tateObject
    (composition := composition)

/-- The inverse formal Tate shift sends the embedded effective Tate object to
Tate degree minus one in the analytic comparison target. -/
theorem TraceAnalyticDMgmComparisonTarget.inverseTateShift_effectiveEmbedding_tateObject :
    (Boundary.Motives.inverseTateShift
        (boundaryEffectiveTateObject (composition := composition))).obj
      ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
          (composition := composition)).obj
        (boundaryEffectiveTateObject (composition := composition))) =
      ⟨boundaryEffectiveTateObject (composition := composition), -1⟩ :=
  Boundary.VoevodskyDMgmInverseTateShift_effectiveEmbedding_tateObject
    (composition := composition)

/-- The analytic comparison target formally inverts the Boundary effective Tate
object. -/
theorem TraceAnalyticDMgmComparisonTarget.formallyInvertsTateObject :
    (Boundary.Motives.inverseTateShift
        (boundaryEffectiveTateObject (composition := composition))).obj
      ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
          (composition := composition)).obj
        (boundaryEffectiveTateObject (composition := composition))) =
      ⟨boundaryEffectiveTateObject (composition := composition), -1⟩ :=
  Boundary.VoevodskyDMgm_formallyInvertsTateObject
    (composition := composition)

end AnalyticMotives
end LFunctions
end Boundary
