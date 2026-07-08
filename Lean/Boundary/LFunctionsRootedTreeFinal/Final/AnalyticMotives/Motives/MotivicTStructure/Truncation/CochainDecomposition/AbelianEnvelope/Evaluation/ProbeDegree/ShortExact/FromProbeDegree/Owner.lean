import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.FromCochain.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.ShortExact.CaseSplit.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.CollectiveEvaluation.Exact.Coordinates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.EpiMono.Owner

/-!
# Degreewise short exactness from probe-degree short exactness

This file reflects the concrete probe-degree Q-module short exactness data
back to the degreewise analytic abelian-envelope short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- A named probe-degree short exactness proof transports to the iterated
degree-then-probe evaluation short complex. -/
theorem abelianEnvelopeCochainDecomposition_iteratedProbeDegreeShortExact_of_probeDegree
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hprobe :
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).ShortExact) :
    (((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
      cut
      complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree)).map
      (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)).ShortExact :=
  Eq.ndrec
    (motive := fun shortComplex => shortComplex.ShortExact)
    hprobe
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_eq_iteratedMap
        cut
        complex
        probe
        degree)

/-- Probe-degree short exactness at every analytic probe implies short
exactness of the corresponding degreewise analytic abelian-envelope short
complex. -/
theorem abelianEnvelopeCochainDecompositionDegreeShortExact_of_probeDegreeShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (hprobe :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).ShortExact) :
    ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree)).ShortExact :=
  TraceAnalyticAdditiveAbelianEnvelope.shortExact_of_exact_mono_epi
    (TraceAnalyticAdditiveAbelianEnvelope.exact_of_evaluation_exact
      (((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveAbelianEnvelope
          (ComplexShape.up ℤ)
          degree)))
      (fun probe =>
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecomposition_iteratedProbeDegreeShortExact_of_probeDegree
            cut
            complex
            probe
            degree
            (hprobe probe)).exact))
    (TraceAnalyticAdditiveAbelianEnvelope.mono_of_componentwise_mono
      (((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveAbelianEnvelope
          (ComplexShape.up ℤ)
          degree)).f)
      (fun object =>
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecomposition_iteratedProbeDegreeShortExact_of_probeDegree
            cut
            complex
            object.unop
            degree
            (hprobe object.unop)).mono_f))
    (TraceAnalyticAdditiveAbelianEnvelope.epi_of_componentwise_epi
      (((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveAbelianEnvelope
          (ComplexShape.up ℤ)
          degree)).g)
      (fun object =>
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecomposition_iteratedProbeDegreeShortExact_of_probeDegree
            cut
            complex
            object.unop
            degree
            (hprobe object.unop)).epi_g))

/-- Casewise probe-degree exactness plus the remaining mono/epi fields imply
short exactness of the corresponding degreewise analytic abelian-envelope
short complex. -/
theorem abelianEnvelopeCochainDecompositionDegreeShortExact_of_probeDegree_casewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (hlowerExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none →
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).Exact)
    (hoffEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).g) :
    ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree)).ShortExact :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDegreeShortExact_of_probeDegreeShortExact
      cut
      complex
      degree
      (fun probe =>
        TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_lowerTail_or_offLowerTail
            cut
            complex
            probe
            (hlowerExact probe)
            (hlowerMono probe)
            (hoffExact probe)
            (hoffEpi probe)
            degree)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
