import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.CaseSplit.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.IsIso.FromIsoHom.Owner

/-!
# Probe-degree exactness from concrete isomorphism formulas

This file assembles the lower-tail and off-lower-tail exactness reductions
when the actual evaluated truncation maps are identified with homs of explicit
`ModuleCat Rat` isomorphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Concrete isomorphism formulas for the lower-tail first map and the
off-lower-tail second map prove exactness of the evaluated truncation short
complex in every degree. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeExact_of_isoHom_caseSplit
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerIso :
      ∀ lowerTail : ℕ,
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).X₁ ≅
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).X₂)
    (lowerMap :
      ∀ lowerTail : ℕ,
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).f =
          (lowerIso lowerTail).hom)
    (offIso :
      ∀ degree : ℤ,
        (TraceAnalyticMotivicTStructure.truncLEEmbedding
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
          none →
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).X₂ ≅
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).X₃)
    (offMap :
      ∀ (degree : ℤ)
        (hnone :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none),
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g =
          (offIso degree hnone).hom)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionProbeDegreeExact_of_lowerTail_or_offLowerTail
      cut
      complex
      probe
      (fun lowerTail =>
        TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionProbeDegreeLowerTailExact_of_f_eq_iso_hom
            cut
            complex
            probe
            lowerTail
            (lowerIso lowerTail)
            (lowerMap lowerTail))
      (fun degree hnone =>
        TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailExact_of_g_eq_iso_hom
            cut
            complex
            probe
            degree
            hnone
            (offIso degree hnone)
            (offMap degree hnone))
      degree

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
