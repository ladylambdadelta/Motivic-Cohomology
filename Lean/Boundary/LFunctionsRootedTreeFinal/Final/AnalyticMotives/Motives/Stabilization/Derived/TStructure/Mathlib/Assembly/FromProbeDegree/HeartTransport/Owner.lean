import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.FromProbeDegree.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.FromProbeDegree.Heart.Equivalence.Owner

/-!
# Probe-degree analytic t-structure payoff

This file packages the strongest current analytic t-structure assembly: global
postcomposition vanishing supplies orthogonality, global probe-degree short
exactness supplies the truncation triangle, and the resulting Mathlib
t-structure has the expected homological heart.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Remaining analytic payoff gap: contour/probe postcomposition vanishing. -/
theorem globalPostcompVanishing_of_traceCalculus :
    ∀ {source target : TraceAnalyticDerivedMotiveCategory},
      ∀ (morphism : source ⟶ target),
        TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
          TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
            ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
              ∀ hom : probe.unop ⟶ source,
                hom ≫ morphism = 0 := by
  sorry

/-- Remaining analytic payoff gap: lower-tail probe-degree exactness. -/
theorem globalProbeDegree_lowerTail_exact_of_traceCalculus :
    ∀ object : TraceAnalyticDerivedMotiveCategory,
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                (lowerTail : ℤ))).Exact := by
  sorry

/-- Remaining analytic payoff gap: lower-tail probe-degree left map is mono. -/
theorem globalProbeDegree_lowerTail_mono_of_traceCalculus :
    ∀ object : TraceAnalyticDerivedMotiveCategory,
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                  (lowerTail : ℤ))).f := by
  sorry

/-- Remaining analytic payoff gap: off-tail probe-degree exactness. -/
theorem globalProbeDegree_offTail_exact_of_traceCalculus :
    ∀ object : TraceAnalyticDerivedMotiveCategory,
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              degree).Exact := by
  sorry

/-- Remaining analytic payoff gap: off-tail probe-degree right map is epi. -/
theorem globalProbeDegree_offTail_epi_of_traceCalculus :
    ∀ object : TraceAnalyticDerivedMotiveCategory,
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).g := by
  sorry

/-- The analytic t-structure obtained after the remaining trace-calculus
gaps are supplied. -/
def tStructureOfTraceCalculus :
    CategoryTheory.Triangulated.TStructure
      TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticDerivedMotiveCategory
    .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
      TraceAnalyticDerivedMotiveCategory.globalPostcompVanishing_of_traceCalculus
      TraceAnalyticDerivedMotiveCategory.globalProbeDegree_lowerTail_exact_of_traceCalculus
      TraceAnalyticDerivedMotiveCategory.globalProbeDegree_lowerTail_mono_of_traceCalculus
      TraceAnalyticDerivedMotiveCategory.globalProbeDegree_offTail_exact_of_traceCalculus
      TraceAnalyticDerivedMotiveCategory.globalProbeDegree_offTail_epi_of_traceCalculus

/-- The postcomposition/global-probe construction gives the analytic
t-structure with its concrete `≤`/`≥` predicates, zero field, truncation
triangle field, and the transported heart equivalence compatible with the
ambient derived-motive inclusions. -/
theorem tStructure_payoff_of_globalPostcompVanishingAndGlobalProbeDegree
    (postcompVanishing :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
                ∀ hom : probe.unop ⟶ source,
                  hom ≫ morphism = 0)
    (hlowerExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ lowerTail : ℕ,
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                  (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ lowerTail : ℕ,
            Mono
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                  1
                  (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                  probe
                  (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                    (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ degree : ℤ,
            (TraceAnalyticMotivicTStructure.truncLEEmbedding
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
                degree =
              none →
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).Exact)
    (hoffEpi :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ degree : ℤ,
            (TraceAnalyticMotivicTStructure.truncLEEmbedding
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
                degree =
              none →
            Epi
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                  1
                  (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                  probe
                  degree).g)
    (cut : ℤ) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi).LE =
      TraceAnalyticDerivedMotiveCategory.tStructureLE ∧
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi).GE =
      TraceAnalyticDerivedMotiveCategory.tStructureGE ∧
    (∀ {source target : TraceAnalyticDerivedMotiveCategory},
      ∀ (morphism : source ⟶ target),
        ∀ (sourceMembership :
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source),
          ∀ (targetMembership :
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target),
            (TraceAnalyticDerivedMotiveCategory
              .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
                postcompVanishing
                hlowerExact
                hlowerMono
                hoffExact
                hoffEpi).zero'
                  morphism
                  sourceMembership
                  targetMembership =
              TraceAnalyticDerivedMotiveCategory
                .zeroField_of_globalPostcompVanishing
                  postcompVanishing
                  morphism
                sourceMembership
                targetMembership) ∧
    (∀ object : TraceAnalyticDerivedMotiveCategory,
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
          postcompVanishing
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi).exists_triangle_zero_one object =
        TraceAnalyticDerivedMotiveCategory
          .existsTriangleZeroOne_of_globalCochainPreimageShortExact
            (TraceAnalyticDerivedMotiveCategory
              .globalCochainPreimageShortExact_of_globalProbeDegree_casewise
                hlowerExact
                hlowerMono
                hoffExact
                hoffEpi)
            object) ∧
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart
      .equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut).functor ⋙
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
            postcompVanishing
            hlowerExact
            hlowerMono
            hoffExact
            hoffEpi)
        cut =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut ∧
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart
      .equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut).inverse ⋙
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
            postcompVanishing
            hlowerExact
            hlowerMono
            hoffExact
            hoffEpi)
        cut :=
  And.intro
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree_LE
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi)
    (And.intro
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree_GE
          postcompVanishing
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)
      (And.intro
        (fun {source target} morphism sourceMembership targetMembership =>
          TraceAnalyticDerivedMotiveCategory
            .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree_zero'
              postcompVanishing
              hlowerExact
              hlowerMono
              hoffExact
              hoffEpi
              morphism
              sourceMembership
              targetMembership)
        (And.intro
          (fun object =>
            TraceAnalyticDerivedMotiveCategory
              .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree_exists_triangle_zero_one
                postcompVanishing
                hlowerExact
                hlowerMono
                hoffExact
                hoffEpi
                object)
          (And.intro
            (TraceAnalyticDerivedMotiveCategory.HomologicalHeart
              .equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree_functor_comp_inclusion
                postcompVanishing
                hlowerExact
                hlowerMono
                hoffExact
                hoffEpi
                cut)
            (TraceAnalyticDerivedMotiveCategory.HomologicalHeart
              .equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree_inverse_comp_inclusion
                postcompVanishing
                hlowerExact
                hlowerMono
                hoffExact
                hoffEpi
                cut))))

/-- The postcomposition/global-probe t-structure transports the homological
heart to the categorical Mathlib heart by an actual equivalence, and both
directions have the expected ambient inclusion. -/
theorem heartEquivalence_payoff_of_globalPostcompVanishingAndGlobalProbeDegree
    (postcompVanishing :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
                ∀ hom : probe.unop ⟶ source,
                  hom ≫ morphism = 0)
    (hlowerExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ lowerTail : ℕ,
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                  (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ lowerTail : ℕ,
            Mono
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                  1
                  (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                  probe
                  (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                    (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ degree : ℤ,
            (TraceAnalyticMotivicTStructure.truncLEEmbedding
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
                degree =
              none →
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).Exact)
    (hoffEpi :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ degree : ℤ,
            (TraceAnalyticMotivicTStructure.truncLEEmbedding
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
                degree =
              none →
            Epi
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                  1
                  (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                  probe
                  degree).g)
    (cut : ℤ) :
    ∃ heartEquivalence :
        TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ≌
          TraceAnalyticDerivedMotiveCategory.TStructureHeart
            (TraceAnalyticDerivedMotiveCategory
              .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
                postcompVanishing
                hlowerExact
                hlowerMono
                hoffExact
                hoffEpi)
            cut,
      heartEquivalence.functor ⋙
        TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
          (TraceAnalyticDerivedMotiveCategory
            .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
              postcompVanishing
              hlowerExact
              hlowerMono
              hoffExact
              hoffEpi)
          cut =
        TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut ∧
      heartEquivalence.inverse ⋙
        TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut =
        TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
          (TraceAnalyticDerivedMotiveCategory
            .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
              postcompVanishing
              hlowerExact
              hlowerMono
              hoffExact
              hoffEpi)
          cut :=
  Exists.intro
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart
      .equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut)
    (And.intro
      (TraceAnalyticDerivedMotiveCategory.HomologicalHeart
        .equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree_functor_comp_inclusion
          postcompVanishing
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi
          cut)
      (TraceAnalyticDerivedMotiveCategory.HomologicalHeart
        .equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree_inverse_comp_inclusion
          postcompVanishing
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi
          cut))

/-- The t-structure payoff with the remaining analytic inputs exposed as
named trace-calculus `sorry`s rather than theorem parameters. -/
theorem tStructure_payoff_of_traceCalculus
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.tStructureOfTraceCalculus.LE =
      TraceAnalyticDerivedMotiveCategory.tStructureLE ∧
    TraceAnalyticDerivedMotiveCategory.tStructureOfTraceCalculus.GE =
      TraceAnalyticDerivedMotiveCategory.tStructureGE ∧
    (∀ {source target : TraceAnalyticDerivedMotiveCategory},
      ∀ (morphism : source ⟶ target),
        ∀ (sourceMembership :
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source),
          ∀ (targetMembership :
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target),
            TraceAnalyticDerivedMotiveCategory.tStructureOfTraceCalculus.zero'
                morphism
                sourceMembership
                targetMembership =
              TraceAnalyticDerivedMotiveCategory
                .zeroField_of_globalPostcompVanishing
                  TraceAnalyticDerivedMotiveCategory.globalPostcompVanishing_of_traceCalculus
                  morphism
                sourceMembership
                targetMembership) ∧
    (∀ object : TraceAnalyticDerivedMotiveCategory,
      TraceAnalyticDerivedMotiveCategory
          .tStructureOfTraceCalculus.exists_triangle_zero_one object =
        TraceAnalyticDerivedMotiveCategory
          .existsTriangleZeroOne_of_globalCochainPreimageShortExact
            (TraceAnalyticDerivedMotiveCategory
              .globalCochainPreimageShortExact_of_globalProbeDegree_casewise
                TraceAnalyticDerivedMotiveCategory.globalProbeDegree_lowerTail_exact_of_traceCalculus
                TraceAnalyticDerivedMotiveCategory.globalProbeDegree_lowerTail_mono_of_traceCalculus
                TraceAnalyticDerivedMotiveCategory.globalProbeDegree_offTail_exact_of_traceCalculus
                TraceAnalyticDerivedMotiveCategory.globalProbeDegree_offTail_epi_of_traceCalculus)
            object) ∧
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart
      .equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree
        TraceAnalyticDerivedMotiveCategory.globalPostcompVanishing_of_traceCalculus
        TraceAnalyticDerivedMotiveCategory.globalProbeDegree_lowerTail_exact_of_traceCalculus
        TraceAnalyticDerivedMotiveCategory.globalProbeDegree_lowerTail_mono_of_traceCalculus
        TraceAnalyticDerivedMotiveCategory.globalProbeDegree_offTail_exact_of_traceCalculus
        TraceAnalyticDerivedMotiveCategory.globalProbeDegree_offTail_epi_of_traceCalculus
        cut).functor ⋙
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        TraceAnalyticDerivedMotiveCategory.tStructureOfTraceCalculus
        cut =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut ∧
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart
      .equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree
        TraceAnalyticDerivedMotiveCategory.globalPostcompVanishing_of_traceCalculus
        TraceAnalyticDerivedMotiveCategory.globalProbeDegree_lowerTail_exact_of_traceCalculus
        TraceAnalyticDerivedMotiveCategory.globalProbeDegree_lowerTail_mono_of_traceCalculus
        TraceAnalyticDerivedMotiveCategory.globalProbeDegree_offTail_exact_of_traceCalculus
        TraceAnalyticDerivedMotiveCategory.globalProbeDegree_offTail_epi_of_traceCalculus
        cut).inverse ⋙
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        TraceAnalyticDerivedMotiveCategory.tStructureOfTraceCalculus
        cut :=
  TraceAnalyticDerivedMotiveCategory
    .tStructure_payoff_of_globalPostcompVanishingAndGlobalProbeDegree
      TraceAnalyticDerivedMotiveCategory.globalPostcompVanishing_of_traceCalculus
      TraceAnalyticDerivedMotiveCategory.globalProbeDegree_lowerTail_exact_of_traceCalculus
      TraceAnalyticDerivedMotiveCategory.globalProbeDegree_lowerTail_mono_of_traceCalculus
      TraceAnalyticDerivedMotiveCategory.globalProbeDegree_offTail_exact_of_traceCalculus
      TraceAnalyticDerivedMotiveCategory.globalProbeDegree_offTail_epi_of_traceCalculus
      cut

/-- The heart-transport payoff with the remaining analytic inputs exposed as
named trace-calculus `sorry`s rather than theorem parameters. -/
theorem heartEquivalence_payoff_of_traceCalculus
    (cut : ℤ) :
    ∃ heartEquivalence :
        TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ≌
          TraceAnalyticDerivedMotiveCategory.TStructureHeart
            TraceAnalyticDerivedMotiveCategory.tStructureOfTraceCalculus
            cut,
      heartEquivalence.functor ⋙
        TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
          TraceAnalyticDerivedMotiveCategory.tStructureOfTraceCalculus
          cut =
        TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut ∧
      heartEquivalence.inverse ⋙
        TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut =
        TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
          TraceAnalyticDerivedMotiveCategory.tStructureOfTraceCalculus
          cut :=
  TraceAnalyticDerivedMotiveCategory
    .heartEquivalence_payoff_of_globalPostcompVanishingAndGlobalProbeDegree
      TraceAnalyticDerivedMotiveCategory.globalPostcompVanishing_of_traceCalculus
      TraceAnalyticDerivedMotiveCategory.globalProbeDegree_lowerTail_exact_of_traceCalculus
      TraceAnalyticDerivedMotiveCategory.globalProbeDegree_lowerTail_mono_of_traceCalculus
      TraceAnalyticDerivedMotiveCategory.globalProbeDegree_offTail_exact_of_traceCalculus
      TraceAnalyticDerivedMotiveCategory.globalProbeDegree_offTail_epi_of_traceCalculus
      cut

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
