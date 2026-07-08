import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Owner

/-!
# Object formulas for the Boundary DMgm comparison target

This file exposes object-level formulas for formal Tate shifts in the concrete
Boundary `DM_gm(Q)_Q` target used by the analytic comparison lane.
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

/-- Formal Tate shift preserves the effective object of a comparison-target
object. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShift_obj_effectiveObj
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    ((Boundary.Motives.tateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        object).effectiveObj =
      object.effectiveObj :=
  rfl

/-- Formal Tate shift increments the Tate degree of a comparison-target object. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShift_obj_tateTwist
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    ((Boundary.Motives.tateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        object).tateTwist =
      object.tateTwist + 1 :=
  rfl

/-- Inverse formal Tate shift preserves the effective object of a comparison-target
object. -/
theorem TraceAnalyticDMgmComparisonTarget.inverseTateShift_obj_effectiveObj
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    ((Boundary.Motives.inverseTateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        object).effectiveObj =
      object.effectiveObj :=
  rfl

/-- Inverse formal Tate shift decrements the Tate degree of a comparison-target object. -/
theorem TraceAnalyticDMgmComparisonTarget.inverseTateShift_obj_tateTwist
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    ((Boundary.Motives.inverseTateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        object).tateTwist =
      object.tateTwist - 1 :=
  rfl

/-- Formal Tate shift sends an effective embedded object to Tate degree one. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShift_obj_effectiveEmbedding
    (object : canonicalEffectiveMotives composition) :
    (Boundary.Motives.tateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
          (composition := composition)).obj object) =
      ⟨object, 1⟩ :=
  rfl

/-- Inverse formal Tate shift sends an effective embedded object to Tate degree
minus one. -/
theorem TraceAnalyticDMgmComparisonTarget.inverseTateShift_obj_effectiveEmbedding
    (object : canonicalEffectiveMotives composition) :
    (Boundary.Motives.inverseTateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
          (composition := composition)).obj object) =
      ⟨object, -1⟩ :=
  rfl

/-- Inverse Tate shift after Tate shift returns the original comparison-target
object. -/
theorem TraceAnalyticDMgmComparisonTarget.inverseTateShift_obj_tateShift_obj
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (Boundary.Motives.inverseTateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        ((Boundary.Motives.tateShift
          (boundaryEffectiveTateObject (composition := composition))).obj object) =
      object :=
  Boundary.Motives.inverseTateShift_obj_tateShift_obj
    (boundaryEffectiveTateObject (composition := composition))
    object

/-- Tate shift after inverse Tate shift returns the original comparison-target
object. -/
theorem TraceAnalyticDMgmComparisonTarget.tateShift_obj_inverseTateShift_obj
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (Boundary.Motives.tateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        ((Boundary.Motives.inverseTateShift
          (boundaryEffectiveTateObject (composition := composition))).obj object) =
      object :=
  Boundary.Motives.tateShift_obj_inverseTateShift_obj
    (boundaryEffectiveTateObject (composition := composition))
    object

end AnalyticMotives
end LFunctions
end Boundary
