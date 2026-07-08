import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Owner

/-!
# Probe-indexed mono and epi inputs for truncation maps

The componentwise presheaf mono/epi conditions for the Yoneda truncation maps
can be supplied by checking the named probe-degree Q-module maps at every
analytic additive probe.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Monicity of the first map in every probe-degree Q-module truncation short
complex supplies componentwise monicity of every degreewise presheaf lower
inclusion map. -/
theorem abelianEnvelopeCochainDecomposition_componentwiseMono_f_of_probeDegree
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hprobe :
      ∀ degree : ℤ,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          Mono
            ((abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).f)) :
    ∀ degree : ℤ,
      ∀ object : Opposite TraceAnalyticAdditiveCategoryObject,
        Mono
          ((((abelianEnvelopeCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).f).app object) :=
  fun degree object => hprobe degree object.unop

/-- Epicity of the second map in every probe-degree Q-module truncation short
complex supplies componentwise epicity of every degreewise presheaf upper
projection map. -/
theorem abelianEnvelopeCochainDecomposition_componentwiseEpi_g_of_probeDegree
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hprobe :
      ∀ degree : ℤ,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          Epi
            ((abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).g)) :
    ∀ degree : ℤ,
      ∀ object : Opposite TraceAnalyticAdditiveCategoryObject,
        Epi
          ((((abelianEnvelopeCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).g).app object) :=
  fun degree object => hprobe degree object.unop

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
