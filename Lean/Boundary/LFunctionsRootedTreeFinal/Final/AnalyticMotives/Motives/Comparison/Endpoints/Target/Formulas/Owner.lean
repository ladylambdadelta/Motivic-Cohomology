import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Objects.Owner

/-!
# Endpoint object and morphism formulas for the Boundary DMgm target

This file exposes the object- and morphism-level formulas for the concrete
parent Boundary `DMgm` target at the comparison endpoint.  The formulas are the
target-side bookkeeping a later analytic-to-`DMgm` comparison functor must
respect.
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

/-- Endpoint formula: the effective embedding preserves the underlying
effective object. -/
theorem TraceAnalyticMotiveComparison.targetEffectiveEmbedding_obj_effectiveObj
    (object : canonicalEffectiveMotives composition) :
    ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition)).obj object).effectiveObj =
      object :=
  TraceAnalyticDMgmComparisonTarget.effectiveEmbedding_obj_effectiveObj
    (composition := composition)
    object

/-- Endpoint formula: the effective embedding places objects in Tate degree
zero. -/
theorem TraceAnalyticMotiveComparison.targetEffectiveEmbedding_obj_tateTwist
    (object : canonicalEffectiveMotives composition) :
    ((TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
        (composition := composition)).obj object).tateTwist =
      0 :=
  TraceAnalyticDMgmComparisonTarget.effectiveEmbedding_obj_tateTwist
    (composition := composition)
    object

/-- Endpoint formula: the effective embedding is identity on underlying
effective morphisms. -/
theorem TraceAnalyticMotiveComparison.targetEffectiveEmbedding_map
    {source target : canonicalEffectiveMotives composition}
    (hom : source ⟶ target) :
    (TraceAnalyticDMgmComparisonTarget.effectiveEmbedding
      (composition := composition)).map hom =
      hom :=
  TraceAnalyticDMgmComparisonTarget.effectiveEmbedding_map
    (composition := composition)
    hom

/-- Endpoint formula: formal Tate shift preserves the effective object. -/
theorem TraceAnalyticMotiveComparison.targetTateShift_obj_effectiveObj
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    ((Boundary.Motives.tateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        object).effectiveObj =
      object.effectiveObj :=
  TraceAnalyticDMgmComparisonTarget.tateShift_obj_effectiveObj
    (composition := composition)
    object

/-- Endpoint formula: formal Tate shift increments Tate degree. -/
theorem TraceAnalyticMotiveComparison.targetTateShift_obj_tateTwist
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    ((Boundary.Motives.tateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        object).tateTwist =
      object.tateTwist + 1 :=
  TraceAnalyticDMgmComparisonTarget.tateShift_obj_tateTwist
    (composition := composition)
    object

/-- Endpoint formula: inverse formal Tate shift preserves the effective object. -/
theorem TraceAnalyticMotiveComparison.targetInverseTateShift_obj_effectiveObj
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    ((Boundary.Motives.inverseTateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        object).effectiveObj =
      object.effectiveObj :=
  TraceAnalyticDMgmComparisonTarget.inverseTateShift_obj_effectiveObj
    (composition := composition)
    object

/-- Endpoint formula: inverse formal Tate shift decrements Tate degree. -/
theorem TraceAnalyticMotiveComparison.targetInverseTateShift_obj_tateTwist
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    ((Boundary.Motives.inverseTateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        object).tateTwist =
      object.tateTwist - 1 :=
  TraceAnalyticDMgmComparisonTarget.inverseTateShift_obj_tateTwist
    (composition := composition)
    object

/-- Endpoint formula: formal Tate shift is identity on underlying target
morphisms. -/
theorem TraceAnalyticMotiveComparison.targetTateShift_map
    {source target :
      TraceAnalyticDMgmComparisonTarget (composition := composition)}
    (hom : source ⟶ target) :
    (Boundary.Motives.tateShift
      (boundaryEffectiveTateObject (composition := composition))).map hom =
      hom :=
  TraceAnalyticDMgmComparisonTarget.tateShift_map
    (composition := composition)
    hom

/-- Endpoint formula: inverse formal Tate shift is identity on underlying
target morphisms. -/
theorem TraceAnalyticMotiveComparison.targetInverseTateShift_map
    {source target :
      TraceAnalyticDMgmComparisonTarget (composition := composition)}
    (hom : source ⟶ target) :
    (Boundary.Motives.inverseTateShift
      (boundaryEffectiveTateObject (composition := composition))).map hom =
      hom :=
  TraceAnalyticDMgmComparisonTarget.inverseTateShift_map
    (composition := composition)
    hom

/-- Endpoint formula: inverse Tate shift after Tate shift returns the original
target object. -/
theorem TraceAnalyticMotiveComparison.targetInverseTateShift_obj_tateShift_obj
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (Boundary.Motives.inverseTateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        ((Boundary.Motives.tateShift
          (boundaryEffectiveTateObject (composition := composition))).obj object) =
      object :=
  TraceAnalyticDMgmComparisonTarget.inverseTateShift_obj_tateShift_obj
    (composition := composition)
    object

/-- Endpoint formula: Tate shift after inverse Tate shift returns the original
target object. -/
theorem TraceAnalyticMotiveComparison.targetTateShift_obj_inverseTateShift_obj
    (object : TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    (Boundary.Motives.tateShift
      (boundaryEffectiveTateObject (composition := composition))).obj
        ((Boundary.Motives.inverseTateShift
          (boundaryEffectiveTateObject (composition := composition))).obj object) =
      object :=
  TraceAnalyticDMgmComparisonTarget.tateShift_obj_inverseTateShift_obj
    (composition := composition)
    object

end AnalyticMotives
end LFunctions
end Boundary
