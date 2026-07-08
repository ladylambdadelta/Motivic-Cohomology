import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.Heart.Equivalence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.Heart.GlobalShortExact.Owner

/-!
# Heart equivalence for global-short-exact assembled t-structures

This file specializes the homological/categorical heart equivalence to the
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

/-- The existing homological heart is equivalent to the categorical heart of
the global-short-exact orthogonality assembly. -/
def HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalShortExact
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
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ≌
      TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndGlobalShortExact
            zeroField
            globalShortExact)
        cut :=
  TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndTruncation
      zeroField
      (TraceAnalyticDerivedMotiveCategory.existsTriangleZeroOne_of_globalCochainPreimageShortExact
          globalShortExact)
      cut

/-- The functor of the global-short-exact heart equivalence is the
homological-to-categorical heart transport functor. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalShortExact_functor
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
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalShortExact
        zeroField
        globalShortExact
        cut).functor =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndGlobalShortExact
        zeroField
        globalShortExact
        cut :=
  rfl

/-- The inverse of the global-short-exact heart equivalence is the
categorical-to-homological heart transport functor. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalShortExact_inverse
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
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalShortExact
        zeroField
        globalShortExact
        cut).inverse =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndGlobalShortExact
        zeroField
        globalShortExact
        cut :=
  rfl

/-- The existing homological heart is equivalent to the categorical heart of
the global-short-exact postcomposition assembly. -/
def HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalShortExact
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
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ≌
      TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfGlobalPostcompVanishingAndGlobalShortExact
            postcompVanishing
            globalShortExact)
        cut :=
  TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalShortExact
    (TraceAnalyticDerivedMotiveCategory.zeroField_of_globalPostcompVanishing
      postcompVanishing)
    globalShortExact
    cut

/-- The functor of the global-short-exact postcomposition heart equivalence is
the homological-to-categorical heart transport functor. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalShortExact_functor
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
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalShortExact
        postcompVanishing
        globalShortExact
        cut).functor =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfGlobalPostcompVanishingAndGlobalShortExact
        postcompVanishing
        globalShortExact
        cut :=
  rfl

/-- The inverse of the global-short-exact postcomposition heart equivalence
is the categorical-to-homological heart transport functor. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalShortExact_inverse
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
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalShortExact
        postcompVanishing
        globalShortExact
        cut).inverse =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfGlobalPostcompVanishingAndGlobalShortExact
        postcompVanishing
        globalShortExact
        cut :=
  rfl

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
