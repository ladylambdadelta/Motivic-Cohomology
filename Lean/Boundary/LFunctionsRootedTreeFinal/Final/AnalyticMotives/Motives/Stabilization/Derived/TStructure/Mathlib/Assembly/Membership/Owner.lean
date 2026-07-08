import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.Projections.Owner

/-!
# Membership bridges for the assembled Mathlib t-structure

This file turns analytic `≤` and `≥` predicate memberships into Mathlib
`TStructure.IsLE` and `TStructure.IsGE` memberships for the assembled analytic
t-structures.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Analytic `≤` membership gives Mathlib `IsLE` membership for the assembled
orthogonality/truncation t-structure. -/
theorem isLE_tStructureOfOrthogonalityAndTruncation_of_tStructureLE
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE degree object) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne).IsLE object degree where
  le := membership

/-- Analytic `≥` membership gives Mathlib `IsGE` membership for the assembled
orthogonality/truncation t-structure. -/
theorem isGE_tStructureOfOrthogonalityAndTruncation_of_tStructureGE
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE degree object) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndTruncation
        zeroField
        existsTriangleZeroOne).IsGE object degree where
  ge := membership

/-- Analytic `≤` membership gives Mathlib `IsLE` membership for the
global-short-exact assembled t-structure. -/
theorem isLE_tStructureOfOrthogonalityAndGlobalShortExact_of_tStructureLE
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE degree object) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndGlobalShortExact
        zeroField
        globalShortExact).IsLE object degree where
  le := membership

/-- Analytic `≥` membership gives Mathlib `IsGE` membership for the
global-short-exact assembled t-structure. -/
theorem isGE_tStructureOfOrthogonalityAndGlobalShortExact_of_tStructureGE
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE degree object) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndGlobalShortExact
        zeroField
        globalShortExact).IsGE object degree where
  ge := membership

/-- Analytic `≤` membership gives Mathlib `IsLE` membership for the
postcomposition/global-short-exact assembled t-structure. -/
theorem isLE_tStructureOfGlobalPostcompVanishingAndGlobalShortExact_of_tStructureLE
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE degree object) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfGlobalPostcompVanishingAndGlobalShortExact
        postcompVanishing
        globalShortExact).IsLE object degree where
  le := membership

/-- Analytic `≥` membership gives Mathlib `IsGE` membership for the
postcomposition/global-short-exact assembled t-structure. -/
theorem isGE_tStructureOfGlobalPostcompVanishingAndGlobalShortExact_of_tStructureGE
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE degree object) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfGlobalPostcompVanishingAndGlobalShortExact
        postcompVanishing
        globalShortExact).IsGE object degree where
  ge := membership

/-- Mathlib `IsLE` membership for the assembled orthogonality/truncation
t-structure gives analytic `≤` membership. -/
theorem tStructureLE_of_isLE_tStructureOfOrthogonalityAndTruncation
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfOrthogonalityAndTruncation
          zeroField
          existsTriangleZeroOne).IsLE object degree) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE degree object :=
  membership.le

/-- Mathlib `IsGE` membership for the assembled orthogonality/truncation
t-structure gives analytic `≥` membership. -/
theorem tStructureGE_of_isGE_tStructureOfOrthogonalityAndTruncation
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfOrthogonalityAndTruncation
          zeroField
          existsTriangleZeroOne).IsGE object degree) :
    TraceAnalyticDerivedMotiveCategory.tStructureGE degree object :=
  membership.ge

/-- Mathlib `IsLE` membership for the global-short-exact assembled
t-structure gives analytic `≤` membership. -/
theorem tStructureLE_of_isLE_tStructureOfOrthogonalityAndGlobalShortExact
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfOrthogonalityAndGlobalShortExact
          zeroField
          globalShortExact).IsLE object degree) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE degree object :=
  membership.le

/-- Mathlib `IsGE` membership for the global-short-exact assembled
t-structure gives analytic `≥` membership. -/
theorem tStructureGE_of_isGE_tStructureOfOrthogonalityAndGlobalShortExact
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfOrthogonalityAndGlobalShortExact
          zeroField
          globalShortExact).IsGE object degree) :
    TraceAnalyticDerivedMotiveCategory.tStructureGE degree object :=
  membership.ge

/-- Mathlib `IsLE` membership for the postcomposition/global-short-exact
assembled t-structure gives analytic `≤` membership. -/
theorem tStructureLE_of_isLE_tStructureOfGlobalPostcompVanishingAndGlobalShortExact
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfGlobalPostcompVanishingAndGlobalShortExact
          postcompVanishing
          globalShortExact).IsLE object degree) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE degree object :=
  membership.le

/-- Mathlib `IsGE` membership for the postcomposition/global-short-exact
assembled t-structure gives analytic `≥` membership. -/
theorem tStructureGE_of_isGE_tStructureOfGlobalPostcompVanishingAndGlobalShortExact
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfGlobalPostcompVanishingAndGlobalShortExact
          postcompVanishing
          globalShortExact).IsGE object degree) :
    TraceAnalyticDerivedMotiveCategory.tStructureGE degree object :=
  membership.ge

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
