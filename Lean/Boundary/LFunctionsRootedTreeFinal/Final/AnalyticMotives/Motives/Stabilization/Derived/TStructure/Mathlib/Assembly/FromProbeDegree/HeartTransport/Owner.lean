import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.FromProbeDegree.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.FromProbeDegree.Heart.Equivalence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Global.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Constructors.TraceCalculus.Owner

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

abbrev TraceCalculusLowerBoundaryExactField : Prop :=
  ∀ object : TraceAnalyticDerivedMotiveCategory,
    ∀ probe : TraceAnalyticAdditiveCategoryObject,
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          1
          (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
          probe
          (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
            (0 : ℤ))).Exact

abbrev TraceCalculusLowerBoundaryMonoField : Prop :=
  ∀ object : TraceAnalyticDerivedMotiveCategory,
    ∀ probe : TraceAnalyticAdditiveCategoryObject,
      Mono
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
            probe
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
              (0 : ℤ))).f

abbrev TraceCalculusUpperBoundaryExactField : Prop :=
  ∀ object : TraceAnalyticDerivedMotiveCategory,
    ∀ probe : TraceAnalyticAdditiveCategoryObject,
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          1
          (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
          probe
          1).Exact

abbrev TraceCalculusUpperBoundaryEpiField : Prop :=
  ∀ object : TraceAnalyticDerivedMotiveCategory,
    ∀ probe : TraceAnalyticAdditiveCategoryObject,
      Epi
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
            probe
            1).g

theorem globalZeroField_of_traceCalculus :
    ∀ {source target : TraceAnalyticDerivedMotiveCategory},
      ∀ (morphism : source ⟶ target),
        TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
          TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
            morphism = 0 :=
  TraceAnalyticDerivedMotiveCategory.globalZeroField_of_homologicalBounds

theorem globalCochainPreimage_shortExact_of_traceCalculus :
    TraceAnalyticDerivedMotiveCategory.TraceCalculusLowerBoundaryExactField →
    TraceAnalyticDerivedMotiveCategory.TraceCalculusLowerBoundaryMonoField →
    TraceAnalyticDerivedMotiveCategory.TraceCalculusUpperBoundaryExactField →
    TraceAnalyticDerivedMotiveCategory.TraceCalculusUpperBoundaryEpiField →
      ∀ object : TraceAnalyticDerivedMotiveCategory,
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)) :=
  fun lowerBoundaryExact lowerBoundaryMono upperBoundaryExact upperBoundaryEpi object =>
    TraceAnalyticDerivedMotiveCategory
      .current_cochainPreimage_shortExact_of_traceCalculus
        object
        (lowerBoundaryExact object)
        (lowerBoundaryMono object)
        (upperBoundaryExact object)
        (upperBoundaryEpi object)

theorem globalPostcompVanishing_of_traceCalculus :
    ∀ {source target : TraceAnalyticDerivedMotiveCategory},
      ∀ (morphism : source ⟶ target),
        TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
          TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
            ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
              ∀ hom : probe.unop ⟶ source,
                hom ≫ morphism = 0 :=
  TraceAnalyticDerivedMotiveCategory
    .globalPostcompVanishing_of_homologicalBounds

theorem globalProbeDegree_lowerTail_exact_of_traceCalculus :
    TraceAnalyticDerivedMotiveCategory.TraceCalculusLowerBoundaryExactField →
      ∀ object : TraceAnalyticDerivedMotiveCategory,
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                (lowerTail : ℤ))).Exact :=
  fun lowerBoundaryExact object =>
    TraceAnalyticDerivedMotiveCategory
      .current_cochainPreimage_probeDegree_lowerTail_exact_of_traceCalculus
        object
        (lowerBoundaryExact object)

theorem globalProbeDegree_lowerTail_mono_of_traceCalculus :
    TraceAnalyticDerivedMotiveCategory.TraceCalculusLowerBoundaryMonoField →
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
                    (lowerTail : ℤ))).f :=
  fun lowerBoundaryMono object =>
    TraceAnalyticDerivedMotiveCategory
      .current_cochainPreimage_probeDegree_lowerTail_mono_of_traceCalculus
        object
        (lowerBoundaryMono object)

/-- Degreewise trace-calculus exactness gives off-tail probe-degree
exactness. -/
theorem globalProbeDegree_offTail_exact_of_traceCalculus :
    TraceAnalyticDerivedMotiveCategory.TraceCalculusUpperBoundaryExactField →
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
              degree).Exact :=
  fun upperBoundaryExact object =>
    TraceAnalyticDerivedMotiveCategory
      .current_cochainPreimage_probeDegree_offTail_exact_of_traceCalculus
        object
        (upperBoundaryExact object)

/-- Degreewise trace-calculus exactness gives off-tail probe-degree right-map
epicity. -/
theorem globalProbeDegree_offTail_epi_of_traceCalculus :
    TraceAnalyticDerivedMotiveCategory.TraceCalculusUpperBoundaryEpiField →
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
                degree).g :=
  fun upperBoundaryEpi object =>
    TraceAnalyticDerivedMotiveCategory
      .current_cochainPreimage_probeDegree_offTail_epi_of_traceCalculus
        object
        (upperBoundaryEpi object)

/-- The analytic t-structure obtained from the two remaining trace-calculus
inputs. -/
def tStructureOfTraceCalculus
    (lowerBoundaryExact :
      TraceAnalyticDerivedMotiveCategory.TraceCalculusLowerBoundaryExactField)
    (lowerBoundaryMono :
      TraceAnalyticDerivedMotiveCategory.TraceCalculusLowerBoundaryMonoField)
    (upperBoundaryExact :
      TraceAnalyticDerivedMotiveCategory.TraceCalculusUpperBoundaryExactField)
    (upperBoundaryEpi :
      TraceAnalyticDerivedMotiveCategory.TraceCalculusUpperBoundaryEpiField) :
    CategoryTheory.Triangulated.TStructure
      TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticDerivedMotiveCategory
    .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
      TraceAnalyticDerivedMotiveCategory.globalPostcompVanishing_of_traceCalculus
      (TraceAnalyticDerivedMotiveCategory
        .globalProbeDegree_lowerTail_exact_of_traceCalculus
          lowerBoundaryExact)
      (TraceAnalyticDerivedMotiveCategory
        .globalProbeDegree_lowerTail_mono_of_traceCalculus
          lowerBoundaryMono)
      (TraceAnalyticDerivedMotiveCategory
        .globalProbeDegree_offTail_exact_of_traceCalculus
          upperBoundaryExact)
      (TraceAnalyticDerivedMotiveCategory
        .globalProbeDegree_offTail_epi_of_traceCalculus
          upperBoundaryEpi)

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

/-- The t-structure payoff specialized to the two named trace-calculus
inputs. -/
theorem tStructure_payoff_of_traceCalculus
    (lowerBoundaryExact :
      TraceAnalyticDerivedMotiveCategory.TraceCalculusLowerBoundaryExactField)
    (lowerBoundaryMono :
      TraceAnalyticDerivedMotiveCategory.TraceCalculusLowerBoundaryMonoField)
    (upperBoundaryExact :
      TraceAnalyticDerivedMotiveCategory.TraceCalculusUpperBoundaryExactField)
    (upperBoundaryEpi :
      TraceAnalyticDerivedMotiveCategory.TraceCalculusUpperBoundaryEpiField)
    (cut : ℤ) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfTraceCalculus
        lowerBoundaryExact
        lowerBoundaryMono
        upperBoundaryExact
        upperBoundaryEpi).LE =
      TraceAnalyticDerivedMotiveCategory.tStructureLE ∧
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfTraceCalculus
        lowerBoundaryExact
        lowerBoundaryMono
        upperBoundaryExact
        upperBoundaryEpi).GE =
      TraceAnalyticDerivedMotiveCategory.tStructureGE ∧
    (∀ {source target : TraceAnalyticDerivedMotiveCategory},
      ∀ (morphism : source ⟶ target),
        ∀ (sourceMembership :
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source),
          ∀ (targetMembership :
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target),
            (TraceAnalyticDerivedMotiveCategory
              .tStructureOfTraceCalculus
                lowerBoundaryExact
                lowerBoundaryMono
                upperBoundaryExact
                upperBoundaryEpi).zero'
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
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfTraceCalculus
          lowerBoundaryExact
          lowerBoundaryMono
          upperBoundaryExact
          upperBoundaryEpi).exists_triangle_zero_one object =
        TraceAnalyticDerivedMotiveCategory
          .existsTriangleZeroOne_of_globalCochainPreimageShortExact
            (TraceAnalyticDerivedMotiveCategory
              .globalCochainPreimageShortExact_of_globalProbeDegree_casewise
                (TraceAnalyticDerivedMotiveCategory
                  .globalProbeDegree_lowerTail_exact_of_traceCalculus
                    lowerBoundaryExact)
                (TraceAnalyticDerivedMotiveCategory
                  .globalProbeDegree_lowerTail_mono_of_traceCalculus
                    lowerBoundaryMono)
                (TraceAnalyticDerivedMotiveCategory
                  .globalProbeDegree_offTail_exact_of_traceCalculus
                    upperBoundaryExact)
                (TraceAnalyticDerivedMotiveCategory
                  .globalProbeDegree_offTail_epi_of_traceCalculus
                    upperBoundaryEpi))
            object) ∧
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart
      .equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree
        TraceAnalyticDerivedMotiveCategory.globalPostcompVanishing_of_traceCalculus
        (TraceAnalyticDerivedMotiveCategory
          .globalProbeDegree_lowerTail_exact_of_traceCalculus
            lowerBoundaryExact)
        (TraceAnalyticDerivedMotiveCategory
          .globalProbeDegree_lowerTail_mono_of_traceCalculus
            lowerBoundaryMono)
        (TraceAnalyticDerivedMotiveCategory
          .globalProbeDegree_offTail_exact_of_traceCalculus
            upperBoundaryExact)
        (TraceAnalyticDerivedMotiveCategory
          .globalProbeDegree_offTail_epi_of_traceCalculus
            upperBoundaryEpi)
        cut).functor ⋙
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfTraceCalculus
            lowerBoundaryExact
            lowerBoundaryMono
            upperBoundaryExact
            upperBoundaryEpi)
        cut =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut ∧
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart
      .equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree
        TraceAnalyticDerivedMotiveCategory.globalPostcompVanishing_of_traceCalculus
        (TraceAnalyticDerivedMotiveCategory
          .globalProbeDegree_lowerTail_exact_of_traceCalculus
            lowerBoundaryExact)
        (TraceAnalyticDerivedMotiveCategory
          .globalProbeDegree_lowerTail_mono_of_traceCalculus
            lowerBoundaryMono)
        (TraceAnalyticDerivedMotiveCategory
          .globalProbeDegree_offTail_exact_of_traceCalculus
            upperBoundaryExact)
        (TraceAnalyticDerivedMotiveCategory
          .globalProbeDegree_offTail_epi_of_traceCalculus
            upperBoundaryEpi)
        cut).inverse ⋙
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfTraceCalculus
            lowerBoundaryExact
            lowerBoundaryMono
            upperBoundaryExact
            upperBoundaryEpi)
        cut :=
  TraceAnalyticDerivedMotiveCategory
    .tStructure_payoff_of_globalPostcompVanishingAndGlobalProbeDegree
      TraceAnalyticDerivedMotiveCategory.globalPostcompVanishing_of_traceCalculus
      (TraceAnalyticDerivedMotiveCategory
        .globalProbeDegree_lowerTail_exact_of_traceCalculus
          lowerBoundaryExact)
      (TraceAnalyticDerivedMotiveCategory
        .globalProbeDegree_lowerTail_mono_of_traceCalculus
          lowerBoundaryMono)
      (TraceAnalyticDerivedMotiveCategory
        .globalProbeDegree_offTail_exact_of_traceCalculus
          upperBoundaryExact)
      (TraceAnalyticDerivedMotiveCategory
        .globalProbeDegree_offTail_epi_of_traceCalculus
          upperBoundaryEpi)
      cut

/-- The heart-transport payoff specialized to the two named trace-calculus
inputs. -/
theorem heartEquivalence_payoff_of_traceCalculus
    (lowerBoundaryExact :
      TraceAnalyticDerivedMotiveCategory.TraceCalculusLowerBoundaryExactField)
    (lowerBoundaryMono :
      TraceAnalyticDerivedMotiveCategory.TraceCalculusLowerBoundaryMonoField)
    (upperBoundaryExact :
      TraceAnalyticDerivedMotiveCategory.TraceCalculusUpperBoundaryExactField)
    (upperBoundaryEpi :
      TraceAnalyticDerivedMotiveCategory.TraceCalculusUpperBoundaryEpiField)
    (cut : ℤ) :
    ∃ heartEquivalence :
        TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ≌
          TraceAnalyticDerivedMotiveCategory.TStructureHeart
            (TraceAnalyticDerivedMotiveCategory
              .tStructureOfTraceCalculus
                lowerBoundaryExact
                lowerBoundaryMono
                upperBoundaryExact
                upperBoundaryEpi)
            cut,
      heartEquivalence.functor ⋙
        TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
          (TraceAnalyticDerivedMotiveCategory
            .tStructureOfTraceCalculus
              lowerBoundaryExact
              lowerBoundaryMono
              upperBoundaryExact
              upperBoundaryEpi)
          cut =
        TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut ∧
      heartEquivalence.inverse ⋙
        TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut =
        TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
          (TraceAnalyticDerivedMotiveCategory
            .tStructureOfTraceCalculus
              lowerBoundaryExact
              lowerBoundaryMono
              upperBoundaryExact
              upperBoundaryEpi)
          cut :=
  TraceAnalyticDerivedMotiveCategory
    .heartEquivalence_payoff_of_globalPostcompVanishingAndGlobalProbeDegree
      TraceAnalyticDerivedMotiveCategory.globalPostcompVanishing_of_traceCalculus
      (TraceAnalyticDerivedMotiveCategory
        .globalProbeDegree_lowerTail_exact_of_traceCalculus
          lowerBoundaryExact)
      (TraceAnalyticDerivedMotiveCategory
        .globalProbeDegree_lowerTail_mono_of_traceCalculus
          lowerBoundaryMono)
      (TraceAnalyticDerivedMotiveCategory
        .globalProbeDegree_offTail_exact_of_traceCalculus
          upperBoundaryExact)
      (TraceAnalyticDerivedMotiveCategory
        .globalProbeDegree_offTail_epi_of_traceCalculus
          upperBoundaryEpi)
      cut

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
