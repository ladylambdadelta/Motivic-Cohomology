import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Exact.Componentwise.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.CaseSplit.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.CollectiveEvaluation.Exact.Coordinates.Owner

/-!
# Intrinsic cochain short exactness from probe-degree casewise exactness

This file assembles intrinsic probe-degree lower-tail/off-tail exactness data
into cochain-level short exactness of the intrinsic abelian-envelope
truncation sequence.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Intrinsic probe-degree casewise exactness plus the remaining mono/epi
fields assemble to cochain-level short exactness of the intrinsic
abelian-envelope truncation short complex. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_probeDegree_casewise
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
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
          cut
          complex) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise_exact_probe_mono_epi
      cut
      complex
      (fun degree =>
        TraceAnalyticAdditiveAbelianEnvelope.exact_of_evaluation_exact
          (((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
                cut
                complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)))
          (fun probe =>
            Eq.ndrec
              (motive := fun shortComplex => shortComplex.Exact)
              ((TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_casewise_exact_mono_epi
                  cut
                  complex
                  probe
                  (hlowerExact probe)
                  (hlowerMono probe)
                  (hoffExact probe)
                  (hoffEpi probe)
                  degree).exact)
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_eq_iteratedMap
                  cut
                  complex
                  probe
                  degree))
      (fun degree probe =>
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_casewise_exact_mono_epi
            cut
            complex
            probe
            (hlowerExact probe)
            (hlowerMono probe)
            (hoffExact probe)
            (hoffEpi probe)
            degree).mono_f)
      (fun degree probe =>
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_casewise_exact_mono_epi
            cut
            complex
            probe
            (hlowerExact probe)
            (hlowerMono probe)
            (hoffExact probe)
            (hoffEpi probe)
            degree).epi_g)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
