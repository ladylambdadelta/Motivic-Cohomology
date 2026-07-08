import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Subcategories.Heart.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.Membership.Owner

/-!
# Heart objects for assembled analytic t-structures

This file packages the categorical heart of an assembled analytic Mathlib
`TStructure` as the full subcategory cut out by simultaneous `≤ cut` and
`≥ cut` membership, and compares it with the existing homological heart.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The cutwise categorical heart of a Mathlib `TStructure` on derived
analytic motives. -/
abbrev TStructureHeart
    (t :
      CategoryTheory.Triangulated.TStructure
        TraceAnalyticDerivedMotiveCategory)
    (cut : ℤ) :=
  CategoryTheory.FullSubcategory
    (fun object : TraceAnalyticDerivedMotiveCategory =>
      t.LE cut object ∧ t.GE cut object)

/-- The ambient derived motive carried by a categorical heart object. -/
def TStructureHeart.object
    {t :
      CategoryTheory.Triangulated.TStructure
        TraceAnalyticDerivedMotiveCategory}
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.TStructureHeart t cut) :
    TraceAnalyticDerivedMotiveCategory :=
  object.obj

/-- The `≤ cut` certificate carried by a categorical heart object. -/
def TStructureHeart.leMembership
    {t :
      CategoryTheory.Triangulated.TStructure
        TraceAnalyticDerivedMotiveCategory}
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.TStructureHeart t cut) :
    t.LE cut object.object :=
  object.property.left

/-- The `≥ cut` certificate carried by a categorical heart object. -/
def TStructureHeart.geMembership
    {t :
      CategoryTheory.Triangulated.TStructure
        TraceAnalyticDerivedMotiveCategory}
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.TStructureHeart t cut) :
    t.GE cut object.object :=
  object.property.right

/-- The inclusion of the categorical heart into derived analytic motives. -/
abbrev TStructureHeart.inclusion
    (t :
      CategoryTheory.Triangulated.TStructure
        TraceAnalyticDerivedMotiveCategory)
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.TStructureHeart t cut ⥤
      TraceAnalyticDerivedMotiveCategory :=
  CategoryTheory.fullSubcategoryInclusion
    (fun object : TraceAnalyticDerivedMotiveCategory =>
      t.LE cut object ∧ t.GE cut object)

/-- The categorical-heart inclusion sends an object to its ambient derived
motive. -/
theorem TStructureHeart.inclusion_obj
    {t :
      CategoryTheory.Triangulated.TStructure
        TraceAnalyticDerivedMotiveCategory}
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.TStructureHeart t cut) :
    (TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion t cut).obj
        object =
      object.object :=
  rfl

/-- Heart membership for the assembled orthogonality/truncation t-structure
is exactly the existing homological heart condition. -/
theorem tStructureHeart_iff_homologicalHeartOfOrthogonalityAndTruncation
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory) :
    ((TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne).LE cut object ∧
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfOrthogonalityAndTruncation
          zeroField
          existsTriangleZeroOne).GE cut object) ↔
      (TraceAnalyticDerivedMotiveCategory.HomologicalGE cut object ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalLE cut object) :=
  Iff.intro
    (fun membership =>
      And.intro
        membership.right
        membership.left)
    (fun membership =>
      And.intro
        membership.right
        membership.left)

/-- A homological heart object determines a heart object for the assembled
orthogonality/truncation t-structure. -/
def HomologicalHeart.toTStructureHeartOfOrthogonalityAndTruncation
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :
    TraceAnalyticDerivedMotiveCategory.TStructureHeart
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfOrthogonalityAndTruncation
          zeroField
          existsTriangleZeroOne)
      cut where
  obj := object.object
  property :=
    And.intro
      (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.upperMembership
        object)
      (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.lowerMembership
        object)

/-- A categorical heart object for the assembled orthogonality/truncation
t-structure determines a homological heart object. -/
def TStructureHeart.toHomologicalHeartOfOrthogonalityAndTruncation
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    {cut : ℤ}
    (object :
      TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndTruncation
            zeroField
            existsTriangleZeroOne)
        cut) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut where
  obj := object.object
  property :=
    And.intro
      object.geMembership
      object.leMembership

/-- The functor from the existing homological heart to the categorical heart
of the assembled orthogonality/truncation t-structure. -/
abbrev HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndTruncation
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ⥤
      TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndTruncation
            zeroField
            existsTriangleZeroOne)
        cut :=
  CategoryTheory.FullSubcategory.lift
    (fun object : TraceAnalyticDerivedMotiveCategory =>
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfOrthogonalityAndTruncation
          zeroField
          existsTriangleZeroOne).LE cut object ∧
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndTruncation
            zeroField
            existsTriangleZeroOne).GE cut object)
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut)
    (fun object =>
      And.intro
        (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.upperMembership
          object)
        (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.lowerMembership
          object))

/-- The functor from the categorical heart of the assembled
orthogonality/truncation t-structure back to the existing homological heart. -/
abbrev TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndTruncation
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndTruncation
            zeroField
            existsTriangleZeroOne)
        cut ⥤
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut :=
  CategoryTheory.FullSubcategory.lift
    (fun object : TraceAnalyticDerivedMotiveCategory =>
      TraceAnalyticDerivedMotiveCategory.HomologicalGE cut object ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalLE cut object)
    (TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfOrthogonalityAndTruncation
          zeroField
          existsTriangleZeroOne)
      cut)
    (fun object =>
      And.intro
        (TraceAnalyticDerivedMotiveCategory.TStructureHeart.geMembership
          object)
        (TraceAnalyticDerivedMotiveCategory.TStructureHeart.leMembership
          object))

/-- The homological-to-categorical heart map preserves ambient objects. -/
theorem HomologicalHeart.toTStructureHeartOfOrthogonalityAndTruncation_object
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne
        object).object =
      object.object :=
  rfl

/-- The homological-to-categorical heart functor sends objects to the
object-level transport. -/
theorem HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndTruncation_obj
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    {cut : ℤ}
    (object : TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne
        cut).obj object =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartOfOrthogonalityAndTruncation
          zeroField
          existsTriangleZeroOne
          object :=
  rfl

/-- Transport from the homological heart to the categorical heart, followed by
the categorical-heart inclusion, is the original homological-heart inclusion. -/
theorem HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndTruncation_comp_inclusion
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndTruncation
          zeroField
          existsTriangleZeroOne
          cut ⋙
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndTruncation
            zeroField
            existsTriangleZeroOne)
        cut =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut :=
  rfl

/-- The categorical-to-homological heart map preserves ambient objects. -/
theorem TStructureHeart.toHomologicalHeartOfOrthogonalityAndTruncation_object
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    {cut : ℤ}
    (object :
      TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndTruncation
            zeroField
            existsTriangleZeroOne)
        cut) :
    (TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne
        object).object =
      object.object :=
  rfl

/-- The categorical-to-homological heart functor sends objects to the
object-level transport. -/
theorem TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndTruncation_obj
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    {cut : ℤ}
    (object :
      TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndTruncation
            zeroField
            existsTriangleZeroOne)
        cut) :
    (TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne
        cut).obj object =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartOfOrthogonalityAndTruncation
          zeroField
          existsTriangleZeroOne
          object :=
  rfl

/-- Transport from the categorical heart to the homological heart, followed by
the homological-heart inclusion, is the original categorical-heart inclusion. -/
theorem TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndTruncation_comp_inclusion
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (existsTriangleZeroOne :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
          (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
          (firstMap : lower ⟶ object)
          (secondMap : object ⟶ upper)
          (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
          Triangle.mk firstMap secondMap connectingMap ∈
            distTriang TraceAnalyticDerivedMotiveCategory)
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndTruncation
          zeroField
          existsTriangleZeroOne
          cut ⋙
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndTruncation
            zeroField
            existsTriangleZeroOne)
        cut :=
  rfl

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
