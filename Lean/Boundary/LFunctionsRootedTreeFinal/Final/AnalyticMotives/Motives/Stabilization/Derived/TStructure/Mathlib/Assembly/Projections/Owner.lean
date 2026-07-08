import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.Owner

/-!
# Projections from the assembled Mathlib t-structure

This file records the definitional projections from the assembled Mathlib
`TStructure` back to the analytic predicates and supplied analytic fields.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The assembled Mathlib t-structure has the analytic `≤` predicate. -/
theorem tStructureOfOrthogonalityAndTruncation_LE
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
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne).LE =
      TraceAnalyticDerivedMotiveCategory.tStructureLE :=
  rfl

/-- The assembled Mathlib t-structure has the analytic `≥` predicate. -/
theorem tStructureOfOrthogonalityAndTruncation_GE
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
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne).GE =
      TraceAnalyticDerivedMotiveCategory.tStructureGE :=
  rfl

/-- The assembled Mathlib t-structure recovers the supplied `zero'` field. -/
theorem tStructureOfOrthogonalityAndTruncation_zero'
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
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (sourceMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source)
    (targetMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne).zero'
          morphism
          sourceMembership
          targetMembership =
      zeroField
        morphism
        sourceMembership
        targetMembership :=
  rfl

/-- The assembled Mathlib t-structure recovers the supplied adjacent
truncation-triangle field. -/
theorem tStructureOfOrthogonalityAndTruncation_exists_triangle_zero_one
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
    (object : TraceAnalyticDerivedMotiveCategory) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne).exists_triangle_zero_one object =
      existsTriangleZeroOne object :=
  rfl

/-- The global-short-exact assembly has the analytic `≤` predicate. -/
theorem tStructureOfOrthogonalityAndGlobalShortExact_LE
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
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndGlobalShortExact
        zeroField
        globalShortExact).LE =
      TraceAnalyticDerivedMotiveCategory.tStructureLE :=
  rfl

/-- The global-short-exact assembly has the analytic `≥` predicate. -/
theorem tStructureOfOrthogonalityAndGlobalShortExact_GE
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
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndGlobalShortExact
        zeroField
        globalShortExact).GE =
      TraceAnalyticDerivedMotiveCategory.tStructureGE :=
  rfl

/-- The global-short-exact assembly recovers the supplied `zero'` field. -/
theorem tStructureOfOrthogonalityAndGlobalShortExact_zero'
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
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)))
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (sourceMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source)
    (targetMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndGlobalShortExact
        zeroField
        globalShortExact).zero'
          morphism
          sourceMembership
          targetMembership =
      zeroField
        morphism
        sourceMembership
        targetMembership :=
  rfl

/-- The global-short-exact assembly recovers the truncation triangle supplied
by the canonical cochain-preimage short-exact field. -/
theorem tStructureOfOrthogonalityAndGlobalShortExact_exists_triangle_zero_one
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
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)))
    (object : TraceAnalyticDerivedMotiveCategory) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndGlobalShortExact
        zeroField
        globalShortExact).exists_triangle_zero_one object =
      TraceAnalyticDerivedMotiveCategory
        .existsTriangleZeroOne_of_globalCochainPreimageShortExact
          globalShortExact
          object :=
  rfl

/-- The global-postcomposition/global-short-exact assembly has the analytic
`≤` predicate. -/
theorem tStructureOfGlobalPostcompVanishingAndGlobalShortExact_LE
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
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfGlobalPostcompVanishingAndGlobalShortExact
        postcompVanishing
        globalShortExact).LE =
      TraceAnalyticDerivedMotiveCategory.tStructureLE :=
  rfl

/-- The global-postcomposition/global-short-exact assembly has the analytic
`≥` predicate. -/
theorem tStructureOfGlobalPostcompVanishingAndGlobalShortExact_GE
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
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfGlobalPostcompVanishingAndGlobalShortExact
        postcompVanishing
        globalShortExact).GE =
      TraceAnalyticDerivedMotiveCategory.tStructureGE :=
  rfl

/-- The global-postcomposition/global-short-exact assembly recovers the
postcomposition-detected `zero'` field. -/
theorem tStructureOfGlobalPostcompVanishingAndGlobalShortExact_zero'
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
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)))
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (sourceMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source)
    (targetMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfGlobalPostcompVanishingAndGlobalShortExact
        postcompVanishing
        globalShortExact).zero'
          morphism
          sourceMembership
          targetMembership =
      TraceAnalyticDerivedMotiveCategory
        .zeroField_of_globalPostcompVanishing
          postcompVanishing
          morphism
          sourceMembership
          targetMembership :=
  rfl

/-- The global-postcomposition/global-short-exact assembly recovers the
truncation triangle supplied by the canonical cochain-preimage short-exact
field. -/
theorem tStructureOfGlobalPostcompVanishingAndGlobalShortExact_exists_triangle_zero_one
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
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)))
    (object : TraceAnalyticDerivedMotiveCategory) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfGlobalPostcompVanishingAndGlobalShortExact
        postcompVanishing
        globalShortExact).exists_triangle_zero_one object =
      TraceAnalyticDerivedMotiveCategory
        .existsTriangleZeroOne_of_globalCochainPreimageShortExact
          globalShortExact
          object :=
  rfl

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
