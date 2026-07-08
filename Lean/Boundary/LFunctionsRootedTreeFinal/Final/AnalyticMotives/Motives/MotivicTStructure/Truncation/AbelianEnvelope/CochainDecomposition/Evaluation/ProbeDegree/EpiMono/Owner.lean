import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Maps.Owner

/-!
# Probe-indexed mono and epi inputs for the intrinsic truncation maps

This file converts monicity and epicity of named probe-degree Q-module maps
into the componentwise presheaf conditions needed for short exactness in the
abelian envelope.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Monicity of the first map in every intrinsic probe-degree Q-module
truncation short complex supplies componentwise monicity of every degreewise
presheaf lower-inclusion map. -/
theorem abelianEnvelopeIntrinsicCochainDecomposition_componentwiseMono_f_of_probeDegree
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hprobe :
      ∀ degree : ℤ,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          Mono
            ((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).f)) :
    ∀ degree : ℤ,
      ∀ object : Opposite TraceAnalyticAdditiveCategoryObject,
        Mono
          ((((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
                cut
                complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).f).app object) :=
  fun degree object => hprobe degree object.unop

/-- Epicity of the second map in every intrinsic probe-degree Q-module
truncation short complex supplies componentwise epicity of every degreewise
presheaf upper-projection map. -/
theorem abelianEnvelopeIntrinsicCochainDecomposition_componentwiseEpi_g_of_probeDegree
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hprobe :
      ∀ degree : ℤ,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          Epi
            ((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).g)) :
    ∀ degree : ℤ,
      ∀ object : Opposite TraceAnalyticAdditiveCategoryObject,
        Epi
          ((((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
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
