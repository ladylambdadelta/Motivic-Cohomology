import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.Heart.Owner

/-!
# Heart functors for global-short-exact assembled t-structures

This file specializes the categorical heart transport functors to the
Mathlib t-structures assembled from global canonical-preimage short exactness.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The homological heart maps functorially to the categorical heart of the
global-short-exact orthogonality assembly. -/
abbrev HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndGlobalShortExact
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
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ⥤
      TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndGlobalShortExact
            zeroField
            globalShortExact)
        cut :=
  TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndTruncation
      zeroField
      (TraceAnalyticDerivedMotiveCategory.existsTriangleZeroOne_of_globalCochainPreimageShortExact
          globalShortExact)
      cut

/-- The categorical heart of the global-short-exact orthogonality assembly
maps functorially back to the homological heart. -/
abbrev TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndGlobalShortExact
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
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndGlobalShortExact
            zeroField
            globalShortExact)
        cut ⥤
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut :=
  TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndTruncation
      zeroField
      (TraceAnalyticDerivedMotiveCategory.existsTriangleZeroOne_of_globalCochainPreimageShortExact
          globalShortExact)
      cut

/-- The homological-to-categorical global-short-exact heart functor preserves
the ambient derived-motive inclusion. -/
theorem HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndGlobalShortExact_comp_inclusion
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
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndGlobalShortExact
          zeroField
          globalShortExact
          cut ⋙
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndGlobalShortExact
            zeroField
            globalShortExact)
        cut =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut :=
  rfl

/-- The categorical-to-homological global-short-exact heart functor preserves
the ambient derived-motive inclusion. -/
theorem TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndGlobalShortExact_comp_inclusion
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
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndGlobalShortExact
          zeroField
          globalShortExact
          cut ⋙
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndGlobalShortExact
            zeroField
            globalShortExact)
        cut :=
  rfl

/-- The homological heart maps functorially to the categorical heart of the
global-short-exact postcomposition assembly. -/
abbrev HomologicalHeart.toTStructureHeartFunctorOfGlobalPostcompVanishingAndGlobalShortExact
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
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ⥤
      TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfGlobalPostcompVanishingAndGlobalShortExact
            postcompVanishing
            globalShortExact)
        cut :=
  TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndGlobalShortExact
      (TraceAnalyticDerivedMotiveCategory.zeroField_of_globalPostcompVanishing
          postcompVanishing)
      globalShortExact
      cut

/-- The categorical heart of the global-short-exact postcomposition assembly
maps functorially back to the homological heart. -/
abbrev TStructureHeart.toHomologicalHeartFunctorOfGlobalPostcompVanishingAndGlobalShortExact
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
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfGlobalPostcompVanishingAndGlobalShortExact
            postcompVanishing
            globalShortExact)
        cut ⥤
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut :=
  TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndGlobalShortExact
      (TraceAnalyticDerivedMotiveCategory.zeroField_of_globalPostcompVanishing
          postcompVanishing)
      globalShortExact
      cut

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
