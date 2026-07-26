import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.YonedaDetection.Components.Owner

/-!
# Assembly of the Mathlib t-structure from analytic fields

This file assembles the actual Mathlib `TStructure` once the two global
analytic fields are supplied: orthogonality for every `≤ 0` to `≥ 1` morphism,
and adjacent truncation triangles for every derived analytic motive.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The analytic predicates assemble into a Mathlib `TStructure` from the
global orthogonality and adjacent truncation-triangle fields. -/
def tStructureOfOrthogonalityAndTruncation
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
            distTriang TraceAnalyticDerivedMotiveCategory) :
    CategoryTheory.Triangulated.TStructure
      TraceAnalyticDerivedMotiveCategory where
  LE := TraceAnalyticDerivedMotiveCategory.tStructureLE
  GE := TraceAnalyticDerivedMotiveCategory.tStructureGE
  LE_closedUnderIsomorphisms :=
    TraceAnalyticDerivedMotiveCategory.tStructureLE_closedUnderIsomorphisms
  GE_closedUnderIsomorphisms :=
    TraceAnalyticDerivedMotiveCategory.tStructureGE_closedUnderIsomorphisms
  LE_shift :=
    fun n a n' h object membership =>
      TraceAnalyticDerivedMotiveCategory.tStructureLE_shift
        n
        a
        n'
        h
        object
        membership
  GE_shift :=
    fun n a n' h object membership =>
      TraceAnalyticDerivedMotiveCategory.tStructureGE_shift
        n
        a
        n'
        h
        object
        membership
  zero' := fun morphism sourceMembership targetMembership =>
    zeroField morphism sourceMembership targetMembership
  LE_zero_le :=
    TraceAnalyticDerivedMotiveCategory.tStructureLE_zero_le
  GE_one_le :=
    TraceAnalyticDerivedMotiveCategory.tStructureGE_one_le
  exists_triangle_zero_one := existsTriangleZeroOne

/-- Global postcomposition vanishing supplies the Mathlib `zero'` field for
the analytic predicates. -/
theorem zeroField_of_globalPostcompVanishing
    (postcompVanishing :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
                ∀ hom : probe.unop ⟶ source,
                  hom ≫ morphism = 0) :
    ∀ {source target : TraceAnalyticDerivedMotiveCategory},
      ∀ (morphism : source ⟶ target),
        TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
          TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
            morphism = 0 :=
  fun morphism sourceMembership targetMembership =>
    TraceAnalyticDerivedMotiveCategory
      .tStructure_zero_field_of_postcomp_eq_zero
        morphism
        sourceMembership
        targetMembership
        (postcompVanishing
          morphism
          sourceMembership
          targetMembership)

/-- Global orthogonality supplies the corresponding postcomposition vanishing
against every probe. -/
theorem globalPostcompVanishing_of_zeroField
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0) :
    ∀ {source target : TraceAnalyticDerivedMotiveCategory},
      ∀ (morphism : source ⟶ target),
        TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
          TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
            ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
              ∀ hom : probe.unop ⟶ source,
                hom ≫ morphism = 0 :=
  fun morphism sourceMembership targetMembership probe hom =>
    Eq.trans
      (congrArg
        (fun map => hom ≫ map)
        (zeroField morphism sourceMembership targetMembership))
      (comp_zero hom)

/-- If the global adjacent preimage short-exact field is known, it supplies
the adjacent truncation-triangle field required by the Mathlib assembly. -/
theorem existsTriangleZeroOne_of_globalCochainPreimageShortExact
    (globalShortExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        TraceAnalyticAbelianCochainComplex.shortExact
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    ∀ object : TraceAnalyticDerivedMotiveCategory,
      ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
        (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
        (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
        (firstMap : lower ⟶ object)
        (secondMap : object ⟶ upper)
        (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
        Triangle.mk firstMap secondMap connectingMap ∈
          distTriang TraceAnalyticDerivedMotiveCategory :=
  fun object =>
    TraceAnalyticDerivedMotiveCategory
      .current_exists_triangle_zero_one_field
        object
        (globalShortExact object)

/-- The Mathlib analytic t-structure assembled from global orthogonality and
global canonical-preimage short exactness. -/
def tStructureOfOrthogonalityAndGlobalShortExact
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (globalShortExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        TraceAnalyticAbelianCochainComplex.shortExact
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    CategoryTheory.Triangulated.TStructure
      TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticDerivedMotiveCategory
    .tStructureOfOrthogonalityAndTruncation
      zeroField
      (TraceAnalyticDerivedMotiveCategory
        .existsTriangleZeroOne_of_globalCochainPreimageShortExact
          globalShortExact)

/-- The Mathlib analytic t-structure assembled from global postcomposition
vanishing and global canonical-preimage short exactness. -/
def tStructureOfGlobalPostcompVanishingAndGlobalShortExact
    (postcompVanishing :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
                ∀ hom : probe.unop ⟶ source,
                  hom ≫ morphism = 0)
    (globalShortExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        TraceAnalyticAbelianCochainComplex.shortExact
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    CategoryTheory.Triangulated.TStructure
      TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticDerivedMotiveCategory
    .tStructureOfOrthogonalityAndGlobalShortExact
      (TraceAnalyticDerivedMotiveCategory
        .zeroField_of_globalPostcompVanishing
          postcompVanishing)
      globalShortExact

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
