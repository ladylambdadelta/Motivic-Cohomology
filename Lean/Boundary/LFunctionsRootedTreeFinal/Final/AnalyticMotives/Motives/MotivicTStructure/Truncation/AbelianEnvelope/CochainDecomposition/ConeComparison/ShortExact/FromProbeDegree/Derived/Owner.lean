import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.ConeComparison.ShortExact.FromProbeDegree.Owner

/-!
# Derived inversion of probe-degree analytic cone comparison

This file is the derived-categorical consequence of the concrete probe-degree
exactness theorem for the intrinsic abelian-envelope normalized cone-to-upper
comparison map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Concrete probe-degree lower-tail and off-lower-tail exactness data make
the intrinsic abelian-envelope normalized cone-to-upper comparison invertible
after derived localization. -/
theorem abelianEnvelopeNormalizedConeComparisonCochainMap_derived_isIso_of_probeDegree_casewise
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hlowerExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).Exact)
    (hoffEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).g) :
    IsIso
      (TraceAnalyticDerivedMotiveCategory.mapOf
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonCochainMap cut complex)) :=
  letI quasiIsoInstance :
      QuasiIso
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonCochainMap cut complex) :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonCochainMap_quasiIso_of_probeDegree_casewise
        cut
        complex
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
  TraceAnalyticDerivedMotiveCategory.mapOf_isIso_of_quasiIso
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonCochainMap cut complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
