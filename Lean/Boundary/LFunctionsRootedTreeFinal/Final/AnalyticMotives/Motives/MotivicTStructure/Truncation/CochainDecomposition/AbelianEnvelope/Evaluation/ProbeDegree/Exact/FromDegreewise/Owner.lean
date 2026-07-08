import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Exact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.FromCochain.Owner

/-!
# Probe-degree exactness from degreewise short exactness

This file composes the degreewise assembly theorem for the Yoneda truncation
short complex with the probe-degree evaluation theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise exactness of the Yoneda abelian-envelope truncation decomposition
implies exactness of every named degree/probe evaluated Q-module short
complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeExact_of_degreewiseExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).Exact)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  abelianEnvelopeCochainDecompositionProbeDegreeExact_of_cochainExact
    cut
    complex
    probe
    degree
    (abelianEnvelopeCochainDecompositionExact_of_degreewise
      cut
      complex
      hdegree)

/-- Degreewise short exactness of the Yoneda abelian-envelope truncation
decomposition implies short exactness of every named degree/probe evaluated
Q-module short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_degreewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).ShortExact :=
  abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_cochainShortExact
    cut
    complex
    probe
    degree
    (abelianEnvelopeCochainDecompositionShortExact_of_degreewise
      cut
      complex
      hdegree)

/-- Degreewise short exactness of the Yoneda abelian-envelope truncation
decomposition implies exactness of every named degree/probe evaluated Q-module
short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeExact_of_degreewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  (abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_degreewise
    cut
    complex
    hdegree
    probe
    degree).exact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
