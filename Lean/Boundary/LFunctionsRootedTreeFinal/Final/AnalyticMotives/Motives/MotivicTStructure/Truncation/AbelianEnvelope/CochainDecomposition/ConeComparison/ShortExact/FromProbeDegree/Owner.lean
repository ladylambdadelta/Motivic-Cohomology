import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.ConeComparison.ShortExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Exact.FromProbeDegree.Owner

/-!
# Cone-comparison quasi-isomorphism from probe-degree exactness

This file supplies the cone-comparison quasi-isomorphism directly from the
concrete probe-degree lower-tail and off-lower-tail exactness fields.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Probe-degree lower-tail and off-lower-tail exactness data make the
intrinsic abelian-envelope normalized cone-to-upper comparison a
quasi-isomorphism. -/
theorem abelianEnvelopeNormalizedConeComparisonCochainMap_quasiIso_of_probeDegree_casewise
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
    QuasiIso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonCochainMap cut complex) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeNormalizedConeComparisonCochainMap_quasiIso
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_probeDegree_casewise
          cut
          complex
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
