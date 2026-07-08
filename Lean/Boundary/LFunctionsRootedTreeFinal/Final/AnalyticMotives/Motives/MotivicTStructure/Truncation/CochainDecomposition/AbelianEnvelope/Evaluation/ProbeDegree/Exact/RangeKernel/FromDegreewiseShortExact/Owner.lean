import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.RangeKernel.FromDegreewise.Owner

/-!
# Range-kernel equality from degreewise short exactness

This file records the concrete range-kernel consequence of degreewise short
exactness of the Yoneda abelian-envelope truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise short exactness of the Yoneda abelian-envelope truncation
decomposition implies the range-kernel equality for every named probe-degree
Q-module truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegree_range_eq_ker_of_degreewiseShortExact
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
    LinearMap.range
        (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).f =
      LinearMap.ker
        (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g :=
  abelianEnvelopeCochainDecompositionProbeDegree_range_eq_ker_of_degreewiseExact
    cut
    complex
    (fun degree => (hdegree degree).exact)
    probe
    degree

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
