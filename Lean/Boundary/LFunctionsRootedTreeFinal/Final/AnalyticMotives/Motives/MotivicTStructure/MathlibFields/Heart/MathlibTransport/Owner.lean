import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Heart.Projections.Owner

/-!
# Reindexed transport between concrete and Mathlib-facing hearts

This file defines the Mathlib-facing heart predicate induced by the assembled
analytic `tStructureLE` and `tStructureGE` fields, and gives the concrete
full-subcategory functors between it and the iso-closed analytic heart.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The Mathlib-facing heart at the reindexed cut `-cut`, expressed as a full
subcategory of the analytic comparison source. -/
abbrev TraceAnalyticMotivicTStructure.HeartMathlibReindexed
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (fun object : TraceAnalyticDMgmComparisonSource =>
      TraceAnalyticMotivicTStructure.tStructureLE (-cut) object ∧
        TraceAnalyticMotivicTStructure.tStructureGE (-cut) object)

namespace TraceAnalyticMotivicTStructure
namespace HeartMathlibReindexed

/-- The ambient stable comparison-source object carried by a Mathlib-facing
reindexed heart object. -/
def object
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :
    TraceAnalyticDMgmComparisonSource :=
  heartObject.obj

/-- The Mathlib-facing heart membership certificate carried by a reindexed
heart object. -/
def membership
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :
    TraceAnalyticMotivicTStructure.tStructureLE (-cut) heartObject.object ∧
      TraceAnalyticMotivicTStructure.tStructureGE (-cut) heartObject.object :=
  heartObject.property

/-- The inclusion of the Mathlib-facing reindexed heart into the stable
comparison source. -/
abbrev inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut ⥤
      TraceAnalyticDMgmComparisonSource :=
  CategoryTheory.fullSubcategoryInclusion
    (fun object : TraceAnalyticDMgmComparisonSource =>
      TraceAnalyticMotivicTStructure.tStructureLE (-cut) object ∧
        TraceAnalyticMotivicTStructure.tStructureGE (-cut) object)

/-- The Mathlib-facing reindexed heart inclusion sends an object to its
ambient object. -/
theorem inclusion_obj
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :
    (TraceAnalyticMotivicTStructure
      .HeartMathlibReindexed.inclusion cut).obj heartObject =
      heartObject.object :=
  rfl

end HeartMathlibReindexed

namespace HeartIsoClosed

/-- An iso-closed analytic heart object as a Mathlib-facing reindexed heart
object. -/
def toMathlibReindexedObject
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut :=
  ⟨
    heartObject.object,
    TraceAnalyticMotivicTStructure.heartAtIsoClosed_to_tStructureHeart
      heartObject.membership
  ⟩

/-- A Mathlib-facing reindexed heart object as an iso-closed analytic heart
object. -/
def ofMathlibReindexedObject
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed cut :=
  ⟨
    heartObject.object,
    TraceAnalyticMotivicTStructure.heartAtIsoClosed_of_tStructureHeart
      heartObject.membership
  ⟩

/-- The iso-closed-to-Mathlib heart object has the same ambient object. -/
theorem toMathlibReindexedObject_object
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.toMathlibReindexedObject heartObject).object =
      heartObject.object :=
  rfl

/-- The Mathlib-to-iso-closed heart object has the same ambient object. -/
theorem ofMathlibReindexedObject_object
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.ofMathlibReindexedObject heartObject).object =
      heartObject.object :=
  rfl

/-- The functor from the iso-closed analytic heart to the Mathlib-facing
reindexed heart. -/
abbrev toMathlibReindexed
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed cut ⥤
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut :=
  CategoryTheory.FullSubcategory.lift
    (fun object : TraceAnalyticDMgmComparisonSource =>
      TraceAnalyticMotivicTStructure.tStructureLE (-cut) object ∧
        TraceAnalyticMotivicTStructure.tStructureGE (-cut) object)
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.inclusion cut)
    (fun heartObject =>
      TraceAnalyticMotivicTStructure.heartAtIsoClosed_to_tStructureHeart
        heartObject.property)

/-- The functor from the Mathlib-facing reindexed heart to the iso-closed
analytic heart. -/
abbrev ofMathlibReindexed
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut ⥤
      TraceAnalyticMotivicTStructure.HeartIsoClosed cut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.heartAtIsoClosed cut)
    (TraceAnalyticMotivicTStructure.HeartMathlibReindexed.inclusion cut)
    (fun heartObject =>
      TraceAnalyticMotivicTStructure.heartAtIsoClosed_of_tStructureHeart
        heartObject.property)

/-- The iso-closed-to-Mathlib heart functor sends objects to the object-level
transport. -/
theorem toMathlibReindexed_obj
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.toMathlibReindexed cut).obj heartObject =
      TraceAnalyticMotivicTStructure
        .HeartIsoClosed.toMathlibReindexedObject heartObject :=
  rfl

/-- The Mathlib-to-iso-closed heart functor sends objects to the object-level
transport. -/
theorem ofMathlibReindexed_obj
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.ofMathlibReindexed cut).obj heartObject =
      TraceAnalyticMotivicTStructure
        .HeartIsoClosed.ofMathlibReindexedObject heartObject :=
  rfl

/-- Iso-closed-to-Mathlib heart transport followed by the Mathlib-facing
heart inclusion recovers the iso-closed heart inclusion. -/
theorem toMathlibReindexed_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed.toMathlibReindexed cut ⋙
        TraceAnalyticMotivicTStructure.HeartMathlibReindexed.inclusion cut =
      TraceAnalyticMotivicTStructure.HeartIsoClosed.inclusion cut :=
  rfl

/-- Mathlib-to-iso-closed heart transport followed by the iso-closed heart
inclusion recovers the Mathlib-facing heart inclusion. -/
theorem ofMathlibReindexed_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed.ofMathlibReindexed cut ⋙
        TraceAnalyticMotivicTStructure.HeartIsoClosed.inclusion cut =
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed.inclusion cut :=
  rfl

/-- Iso-closed-to-Mathlib heart transport and back is the identity functor on
the iso-closed analytic heart. -/
theorem toMathlibReindexed_comp_ofMathlibReindexed
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed.toMathlibReindexed cut ⋙
        TraceAnalyticMotivicTStructure.HeartIsoClosed.ofMathlibReindexed cut =
      𝟭 (TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :=
  rfl

/-- Mathlib-to-iso-closed heart transport and back is the identity functor on
the Mathlib-facing reindexed heart. -/
theorem ofMathlibReindexed_comp_toMathlibReindexed
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed.ofMathlibReindexed cut ⋙
        TraceAnalyticMotivicTStructure.HeartIsoClosed.toMathlibReindexed cut =
      𝟭 (TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :=
  rfl

/-- Transport from the iso-closed heart to the Mathlib-facing heart and back
preserves the ambient object. -/
theorem ofMathlibReindexed_toMathlibReindexed_object
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    ((TraceAnalyticMotivicTStructure
      .HeartIsoClosed.ofMathlibReindexed cut).obj
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.toMathlibReindexed cut).obj heartObject)).object =
      heartObject.object :=
  rfl

/-- Transport from the Mathlib-facing heart to the iso-closed heart and back
preserves the ambient object. -/
theorem toMathlibReindexed_ofMathlibReindexed_object
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :
    ((TraceAnalyticMotivicTStructure
      .HeartIsoClosed.toMathlibReindexed cut).obj
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.ofMathlibReindexed cut).obj heartObject)).object =
      heartObject.object :=
  rfl

/-- The categorical equivalence between the iso-closed analytic heart and the
Mathlib-facing reindexed heart. -/
def mathlibReindexedEquivalence
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed cut ≌
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut :=
  CategoryTheory.Equivalence.mk
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.toMathlibReindexed cut)
    (TraceAnalyticMotivicTStructure.HeartIsoClosed.ofMathlibReindexed cut)
    (eqToIso
      (Eq.symm
        (TraceAnalyticMotivicTStructure
          .HeartIsoClosed.toMathlibReindexed_comp_ofMathlibReindexed cut)))
    (eqToIso
      (TraceAnalyticMotivicTStructure
        .HeartIsoClosed.ofMathlibReindexed_comp_toMathlibReindexed cut))

/-- The functor of the concrete heart equivalence is the
iso-closed-to-Mathlib transport functor. -/
theorem mathlibReindexedEquivalence_functor
    (cut : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).functor =
      TraceAnalyticMotivicTStructure.HeartIsoClosed.toMathlibReindexed cut :=
  rfl

/-- The inverse of the concrete heart equivalence is the Mathlib-to-iso-closed
transport functor. -/
theorem mathlibReindexedEquivalence_inverse
    (cut : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).inverse =
      TraceAnalyticMotivicTStructure.HeartIsoClosed.ofMathlibReindexed cut :=
  rfl

/-- The functor of the concrete heart equivalence preserves the ambient
comparison-source inclusion. -/
theorem mathlibReindexedEquivalence_functor_comp_inclusion
    (cut : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).functor ⋙
        TraceAnalyticMotivicTStructure.HeartMathlibReindexed.inclusion cut =
      TraceAnalyticMotivicTStructure.HeartIsoClosed.inclusion cut :=
  rfl

/-- The inverse of the concrete heart equivalence preserves the ambient
comparison-source inclusion. -/
theorem mathlibReindexedEquivalence_inverse_comp_inclusion
    (cut : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).inverse ⋙
        TraceAnalyticMotivicTStructure.HeartIsoClosed.inclusion cut =
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed.inclusion cut :=
  rfl

/-- The functor of the concrete heart equivalence sends objects to the
iso-closed-to-Mathlib object transport. -/
theorem mathlibReindexedEquivalence_functor_obj
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).functor.obj
        heartObject =
      TraceAnalyticMotivicTStructure
        .HeartIsoClosed.toMathlibReindexedObject heartObject :=
  rfl

/-- The inverse of the concrete heart equivalence sends objects to the
Mathlib-to-iso-closed object transport. -/
theorem mathlibReindexedEquivalence_inverse_obj
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).inverse.obj
        heartObject =
      TraceAnalyticMotivicTStructure
        .HeartIsoClosed.ofMathlibReindexedObject heartObject :=
  rfl

/-- The functor of the concrete heart equivalence acts as the same ambient
morphism on iso-closed heart morphisms. -/
theorem mathlibReindexedEquivalence_functor_map
    {cut : ℤ}
    {source target :
      TraceAnalyticMotivicTStructure.HeartIsoClosed cut}
    (morphism : source ⟶ target) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).functor.map
        morphism =
      morphism :=
  rfl

/-- The inverse of the concrete heart equivalence acts as the same ambient
morphism on Mathlib-facing heart morphisms. -/
theorem mathlibReindexedEquivalence_inverse_map
    {cut : ℤ}
    {source target :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut}
    (morphism : source ⟶ target) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).inverse.map
        morphism =
      morphism :=
  rfl

/-- The counit of the concrete heart equivalence is the `eqToIso` attached to
the Mathlib-to-iso-closed round-trip identity. -/
theorem mathlibReindexedEquivalence_counitIso
    (cut : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).counitIso =
      eqToIso
        (TraceAnalyticMotivicTStructure
          .HeartIsoClosed.ofMathlibReindexed_comp_toMathlibReindexed cut) :=
  rfl

/-- The counit component of the concrete heart equivalence is the component of
the defining `eqToIso`. -/
theorem mathlibReindexedEquivalence_counit_hom_app
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).counitIso.hom.app
        heartObject =
      (eqToIso
        (TraceAnalyticMotivicTStructure
          .HeartIsoClosed.ofMathlibReindexed_comp_toMathlibReindexed cut))
        .hom.app heartObject :=
  rfl

/-- The inverse counit component of the concrete heart equivalence is the
inverse component of the defining `eqToIso`. -/
theorem mathlibReindexedEquivalence_counit_inv_app
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).counitIso.inv.app
        heartObject =
      (eqToIso
        (TraceAnalyticMotivicTStructure
          .HeartIsoClosed.ofMathlibReindexed_comp_toMathlibReindexed cut))
        .inv.app heartObject :=
  rfl

/-- The unit component at an inverse-image object is determined by the inverse
image of the counit inverse component. -/
theorem mathlibReindexedEquivalence_unit_hom_app_inverse
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).unitIso.hom.app
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence cut).inverse.obj
            heartObject) =
      (TraceAnalyticMotivicTStructure
        .HeartIsoClosed.mathlibReindexedEquivalence cut).inverse.map
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence cut).counitIso.inv.app
            heartObject) :=
  CategoryTheory.Equivalence.unit_app_inverse
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut)
    heartObject

/-- The inverse unit component at an inverse-image object is determined by the
inverse image of the counit component. -/
theorem mathlibReindexedEquivalence_unit_inv_app_inverse
    {cut : ℤ}
    (heartObject :
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed cut) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut).unitIso.inv.app
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence cut).inverse.obj
            heartObject) =
      (TraceAnalyticMotivicTStructure
        .HeartIsoClosed.mathlibReindexedEquivalence cut).inverse.map
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence cut).counitIso.hom.app
            heartObject) :=
  CategoryTheory.Equivalence.unitInv_app_inverse
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence cut)
    heartObject

end HeartIsoClosed
end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
