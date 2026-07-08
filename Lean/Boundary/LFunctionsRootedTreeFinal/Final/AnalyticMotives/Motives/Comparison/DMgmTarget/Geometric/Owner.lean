import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.EffectiveTensor.Owner

/-!
# Geometric Boundary DMgm target for analytic comparison

This file exposes the Boundary geometric stabilized motive category under the
analytic comparison target names.  The construction is the existing Boundary
formal Tate stabilization of geometric effective motives at the restricted
Tate-action functor.
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

/-- Boundary Tate-action data used to stabilize geometric effective motives in
the analytic comparison target. -/
abbrev TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData :=
  BoundaryTateTwistFunctorConstructionData
    (composition := composition)
    (boundaryCanonicalTateObjectConstructionData (composition := composition))

/-- The analytic comparison target's geometric effective Tate-twist functor is
the Boundary restricted Tate-action functor. -/
def TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition)) :
    TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition) ⥤
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition) :=
  Boundary.boundaryGeometricEffectiveTateTwistFunctor
    (composition := composition) twistData

/-- The analytic geometric Tate-twist functor is the Boundary restricted
Tate-action functor. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor_eq_boundary
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition)) :
    TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
        (composition := composition) twistData =
      Boundary.boundaryGeometricEffectiveTateTwistFunctor
        (composition := composition) twistData :=
  rfl

/-- Object formula for the analytic geometric effective Tate-twist functor. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor_obj_val
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    ((TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
      (composition := composition) twistData).obj object).1 =
      twistData.functor.obj object.1 :=
  rfl

/-- Map formula for the analytic geometric effective Tate-twist functor. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor_map
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    {source target :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)}
    (hom : source ⟶ target) :
    (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
      (composition := composition) twistData).map hom =
      twistData.functor.map hom :=
  rfl

/-- The geometric stabilized Boundary target entering the analytic comparison. -/
abbrev TraceAnalyticDMgmComparisonTarget.geometricMotives
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition)) :=
  Boundary.boundaryCanonicalGeometricMotives
    (composition := composition) twistData

/-- The analytic geometric target is the Boundary canonical geometric motive
stabilization. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricMotives_eq_boundary
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition)) :
    TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData =
      Boundary.boundaryCanonicalGeometricMotives
        (composition := composition) twistData :=
  rfl

/-- Embedding of geometric effective motives into the analytic geometric target. -/
def TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition)) :
    TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition) ⥤
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData :=
  Boundary.boundaryCanonicalGeometricEffectiveEmbedding
    (composition := composition) twistData

/-- The analytic geometric effective embedding is the Boundary geometric
effective embedding. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding_eq_boundary
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition)) :
    TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding
        (composition := composition) twistData =
      Boundary.boundaryCanonicalGeometricEffectiveEmbedding
        (composition := composition) twistData :=
  rfl

/-- Geometric effective motives enter the analytic geometric target with their
original effective object. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding_obj_effectiveObj
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    ((TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding
      (composition := composition) twistData).obj object).effectiveObj =
      object :=
  rfl

/-- Geometric effective motives enter the analytic geometric target in Tate
degree zero. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding_obj_tateTwist
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    ((TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding
      (composition := composition) twistData).obj object).tateTwist =
      0 :=
  rfl

/-- The analytic geometric effective embedding acts as the identity on
geometric effective morphisms in the formal Tate-stabilized target. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding_map
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    {source target :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)}
    (hom : source ⟶ target) :
    (TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding
      (composition := composition) twistData).map hom =
      hom :=
  rfl

/-- Geometric Tate shift sends an embedded geometric effective object to Tate
degree one. -/
theorem TraceAnalyticDMgmComparisonTarget.geometric_tateShift_effectiveEmbedding_obj
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    (Boundary.Motives.tateShift
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj
      ((TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding
        (composition := composition) twistData).obj object) =
      ⟨object, 1⟩ :=
  rfl

/-- Inverse geometric Tate shift sends an embedded geometric effective object
to Tate degree minus one. -/
theorem TraceAnalyticDMgmComparisonTarget.geometric_inverseTateShift_effectiveEmbedding_obj
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (object :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)) :
    (Boundary.Motives.inverseTateShift
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj
      ((TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding
        (composition := composition) twistData).obj object) =
      ⟨object, -1⟩ :=
  rfl

/-- Geometric Tate shift sends an embedded geometric effective morphism to the
same underlying morphism. -/
theorem TraceAnalyticDMgmComparisonTarget.geometric_tateShift_effectiveEmbedding_map
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    {source target :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)}
    (hom : source ⟶ target) :
    (Boundary.Motives.tateShift
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).map
      ((TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding
        (composition := composition) twistData).map hom) =
      hom :=
  rfl

/-- Inverse geometric Tate shift sends an embedded geometric effective morphism
to the same underlying morphism. -/
theorem TraceAnalyticDMgmComparisonTarget.geometric_inverseTateShift_effectiveEmbedding_map
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    {source target :
      TraceAnalyticDMgmComparisonTarget.effectiveGeometricMotives
        (composition := composition)}
    (hom : source ⟶ target) :
    (Boundary.Motives.inverseTateShift
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).map
      ((TraceAnalyticDMgmComparisonTarget.geometricEffectiveEmbedding
        (composition := composition) twistData).map hom) =
      hom :=
  rfl

/-- Tate-shift equivalence on the analytic geometric target. -/
def TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition)) :
    TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData ≌
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData :=
  Boundary.boundaryCanonicalGeometricMotivesTateShiftEquivalence
    (composition := composition) twistData

/-- The analytic geometric Tate-shift equivalence is the Boundary geometric
Tate-shift equivalence. -/
theorem TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence_eq_boundary
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition)) :
    TraceAnalyticDMgmComparisonTarget.geometricTateShiftEquivalence
        (composition := composition) twistData =
      Boundary.boundaryCanonicalGeometricMotivesTateShiftEquivalence
        (composition := composition) twistData :=
  rfl

/-- Tate shift on the analytic geometric target increments the Tate degree and
preserves the effective object. -/
theorem TraceAnalyticDMgmComparisonTarget.geometric_tateShift_obj
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (object :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) :
    (Boundary.Motives.tateShift
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj object =
      ⟨object.effectiveObj, object.tateTwist + 1⟩ :=
  rfl

/-- Inverse Tate shift on the analytic geometric target decrements the Tate
degree and preserves the effective object. -/
theorem TraceAnalyticDMgmComparisonTarget.geometric_inverseTateShift_obj
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (object :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) :
    (Boundary.Motives.inverseTateShift
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj object =
      ⟨object.effectiveObj, object.tateTwist - 1⟩ :=
  rfl

/-- Tate shift acts as the identity on morphisms of the analytic geometric
target. -/
theorem TraceAnalyticDMgmComparisonTarget.geometric_tateShift_map
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    {source target :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData}
    (hom : source ⟶ target) :
    (Boundary.Motives.tateShift
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).map hom =
      hom :=
  rfl

/-- Inverse Tate shift acts as the identity on morphisms of the analytic
geometric target. -/
theorem TraceAnalyticDMgmComparisonTarget.geometric_inverseTateShift_map
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    {source target :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData}
    (hom : source ⟶ target) :
    (Boundary.Motives.inverseTateShift
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).map hom =
      hom :=
  rfl

/-- Inverse Tate shift after Tate shift returns the original analytic geometric
target object. -/
theorem TraceAnalyticDMgmComparisonTarget.geometric_inverseTateShift_tateShift
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (object :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) :
    (Boundary.Motives.inverseTateShift
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj
      ((Boundary.Motives.tateShift
          (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
            (composition := composition) twistData)).obj object) =
      object :=
  Boundary.Motives.inverseTateShift_obj_tateShift_obj
    (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
      (composition := composition) twistData)
    object

/-- Tate shift after inverse Tate shift returns the original analytic geometric
target object. -/
theorem TraceAnalyticDMgmComparisonTarget.geometric_tateShift_inverseTateShift
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (object :
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData) :
    (Boundary.Motives.tateShift
        (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj
      ((Boundary.Motives.inverseTateShift
          (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
            (composition := composition) twistData)).obj object) =
      object :=
  Boundary.Motives.tateShift_obj_inverseTateShift_obj
    (TraceAnalyticDMgmComparisonTarget.geometricEffectiveTateTwistFunctor
      (composition := composition) twistData)
    object

end AnalyticMotives
end LFunctions
end Boundary
