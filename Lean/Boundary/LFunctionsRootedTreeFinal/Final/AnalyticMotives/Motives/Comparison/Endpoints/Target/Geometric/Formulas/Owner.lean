import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Owner

/-!
# Endpoint formulas for the geometric Boundary DMgm target

This file exposes the geometric subtarget of the parent Boundary `DMgm` at the
analytic comparison endpoint.  It records the restricted Tate action, the
geometric effective embedding, and the geometric Tate-shift formulas that a
later weight-triangular comparison must preserve.
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

/-- Endpoint geometric target as the Boundary stabilized geometric motive
category. -/
abbrev TraceAnalyticMotiveComparison.geometricTarget :=
  TraceAnalyticDMgmComparisonTarget.geometricMotives
    (composition := composition) twistData

/-- Endpoint geometric target is the Boundary canonical geometric motive
stabilization. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_eq_boundary :
    TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData =
      Boundary.boundaryCanonicalGeometricMotives
        (composition := composition) twistData :=
  TraceAnalyticDMgmComparisonTarget.geometricMotives_eq_boundary
    (composition := composition)
    twistData

/-- Endpoint restricted Tate-action functor on geometric effective motives. -/
def TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor :
    TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition) ⥤
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition) :=
  TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
    (composition := composition) twistData

/-- Endpoint restricted Tate-action functor is the Boundary geometric
Tate-action functor. -/
theorem TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor_eq_boundary :
    TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
        (composition := composition) twistData =
      Boundary.boundaryGeometricEffectiveTateTwistFunctor
        (composition := composition) twistData :=
  TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor_eq_boundary
    (composition := composition)
    twistData

/-- Endpoint object formula for the restricted geometric Tate action. -/
theorem TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor_obj_val
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    ((TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
      (composition := composition) twistData).obj object).1 =
      twistData.functor.obj object.1 :=
  TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor_obj_val
    (composition := composition)
    twistData
    object

/-- Endpoint map formula for the restricted geometric Tate action. -/
theorem TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor_map
    {source target :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
      (composition := composition) twistData).map hom =
      twistData.functor.map hom :=
  TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor_map
    (composition := composition)
    twistData
    hom

/-- Endpoint embedding of geometric effective motives into the geometric
target. -/
def TraceAnalyticMotiveComparison.geometricEffectiveEmbedding :
    TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition) ⥤
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData :=
  TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding
    (composition := composition) twistData

/-- Endpoint geometric effective embedding is the Boundary embedding. -/
theorem TraceAnalyticMotiveComparison.geometricEffectiveEmbedding_eq_boundary :
    TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
        (composition := composition) twistData =
      Boundary.boundaryCanonicalGeometricEffectiveEmbedding
        (composition := composition) twistData :=
  TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding_eq_boundary
    (composition := composition)
    twistData

/-- Endpoint formula: geometric effective embedding preserves the effective
object. -/
theorem TraceAnalyticMotiveComparison.geometricEffectiveEmbedding_obj_effectiveObj
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    ((TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
      (composition := composition) twistData).obj object).effectiveObj =
      object :=
  TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding_obj_effectiveObj
    (composition := composition)
    twistData
    object

/-- Endpoint formula: geometric effective embedding places objects in Tate
degree zero. -/
theorem TraceAnalyticMotiveComparison.geometricEffectiveEmbedding_obj_tateTwist
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    ((TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
      (composition := composition) twistData).obj object).tateTwist =
      0 :=
  TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding_obj_tateTwist
    (composition := composition)
    twistData
    object

/-- Endpoint formula: geometric effective embedding is identity on underlying
geometric effective morphisms. -/
theorem TraceAnalyticMotiveComparison.geometricEffectiveEmbedding_map
    {source target :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
      (composition := composition) twistData).map hom =
      hom :=
  TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding_map
    (composition := composition)
    twistData
    hom

/-- Endpoint Tate-shift equivalence on the geometric target. -/
def TraceAnalyticMotiveComparison.geometricTateShiftEquivalence :
    TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData ≌
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData :=
  TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence
    (composition := composition) twistData

/-- Endpoint geometric Tate-shift equivalence is the Boundary equivalence. -/
theorem TraceAnalyticMotiveComparison.geometricTateShiftEquivalence_eq_boundary :
    TraceAnalyticMotiveComparison.geometricTateShiftEquivalence
        (composition := composition) twistData =
      Boundary.boundaryCanonicalGeometricMotivesTateShiftEquivalence
        (composition := composition) twistData :=
  TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_eq_boundary
    (composition := composition)
    twistData

/-- Endpoint formula: geometric Tate shift sends embedded effective objects to
Tate degree one. -/
theorem TraceAnalyticMotiveComparison.geometric_tateShift_effectiveEmbedding_obj
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    (Boundary.Motives.tateShift
        (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj
      ((TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
        (composition := composition) twistData).obj object) =
      ⟨object, 1⟩ :=
  TraceAnalyticDMgmComparisonTarget.geometric_tateShift_effectiveEmbedding_obj
    (composition := composition)
    twistData
    object

/-- Endpoint formula: inverse geometric Tate shift sends embedded effective
objects to Tate degree minus one. -/
theorem TraceAnalyticMotiveComparison.geometric_inverseTateShift_effectiveEmbedding_obj
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    (Boundary.Motives.inverseTateShift
        (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj
      ((TraceAnalyticMotiveComparison.geometricEffectiveEmbedding
        (composition := composition) twistData).obj object) =
      ⟨object, -1⟩ :=
  TraceAnalyticDMgmComparisonTarget.geometric_inverseTateShift_effectiveEmbedding_obj
    (composition := composition)
    twistData
    object

/-- Endpoint formula: geometric Tate shift increments Tate degree and preserves
the effective object. -/
theorem TraceAnalyticMotiveComparison.geometric_tateShift_obj
    (object :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData) :
    (Boundary.Motives.tateShift
        (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj object =
      ⟨object.effectiveObj, object.tateTwist + 1⟩ :=
  TraceAnalyticDMgmComparisonTarget.geometric_tateShift_obj
    (composition := composition)
    twistData
    object

/-- Endpoint formula: inverse geometric Tate shift decrements Tate degree and
preserves the effective object. -/
theorem TraceAnalyticMotiveComparison.geometric_inverseTateShift_obj
    (object :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData) :
    (Boundary.Motives.inverseTateShift
        (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj object =
      ⟨object.effectiveObj, object.tateTwist - 1⟩ :=
  TraceAnalyticDMgmComparisonTarget.geometric_inverseTateShift_obj
    (composition := composition)
    twistData
    object

/-- Endpoint formula: geometric Tate shift is identity on underlying
morphisms. -/
theorem TraceAnalyticMotiveComparison.geometric_tateShift_map
    {source target :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData}
    (hom : source ⟶ target) :
    (Boundary.Motives.tateShift
        (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).map hom =
      hom :=
  TraceAnalyticDMgmComparisonTarget.geometric_tateShift_map
    (composition := composition)
    twistData
    hom

/-- Endpoint formula: inverse geometric Tate shift is identity on underlying
morphisms. -/
theorem TraceAnalyticMotiveComparison.geometric_inverseTateShift_map
    {source target :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData}
    (hom : source ⟶ target) :
    (Boundary.Motives.inverseTateShift
        (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).map hom =
      hom :=
  TraceAnalyticDMgmComparisonTarget.geometric_inverseTateShift_map
    (composition := composition)
    twistData
    hom

/-- Endpoint formula: inverse Tate shift after Tate shift returns the original
geometric target object. -/
theorem TraceAnalyticMotiveComparison.geometric_inverseTateShift_tateShift
    (object :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData) :
    (Boundary.Motives.inverseTateShift
        (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj
      ((Boundary.Motives.tateShift
          (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
            (composition := composition) twistData)).obj object) =
      object :=
  TraceAnalyticDMgmComparisonTarget.geometric_inverseTateShift_tateShift
    (composition := composition)
    twistData
    object

/-- Endpoint formula: Tate shift after inverse Tate shift returns the original
geometric target object. -/
theorem TraceAnalyticMotiveComparison.geometric_tateShift_inverseTateShift
    (object :
      TraceAnalyticMotiveComparison.geometricTarget
        (composition := composition) twistData) :
    (Boundary.Motives.tateShift
        (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj
      ((Boundary.Motives.inverseTateShift
          (TraceAnalyticMotiveComparison.geometricEffectiveTateTwistFunctor
            (composition := composition) twistData)).obj object) =
      object :=
  TraceAnalyticDMgmComparisonTarget.geometric_tateShift_inverseTateShift
    (composition := composition)
    twistData
    object

end AnalyticMotives
end LFunctions
end Boundary
