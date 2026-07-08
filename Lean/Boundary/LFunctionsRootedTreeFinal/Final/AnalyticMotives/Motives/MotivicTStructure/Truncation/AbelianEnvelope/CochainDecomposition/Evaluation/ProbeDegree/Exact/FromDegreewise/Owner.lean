import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Exact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Exact.FromCochain.Owner

/-!
# Intrinsic probe-degree exactness from degreewise exactness

This file composes the intrinsic degreewise assembly theorem with the
probe-degree evaluation theorem for the abelian-envelope normalized truncation
decomposition.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise exactness of the intrinsic abelian-envelope truncation
decomposition implies exactness of every named degree/probe evaluated Q-module
short complex. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeExact_of_degreewiseExact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).Exact)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).Exact :=
  abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeExact_of_cochainExact
    cut
    complex
    probe
    degree
    (abelianEnvelopeIntrinsicCochainDecompositionExact_of_degreewise
      cut
      complex
      hdegree)

/-- Degreewise short exactness of the intrinsic abelian-envelope truncation
decomposition implies short exactness of every named degree/probe evaluated
Q-module short complex. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_degreewise
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).ShortExact :=
  abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_cochainShortExact
    cut
    complex
    probe
    degree
    (abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise
      cut
      complex
      hdegree)

/-- Degreewise short exactness of the intrinsic abelian-envelope truncation
decomposition implies exactness of every named degree/probe evaluated Q-module
short complex. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeExact_of_degreewise
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).Exact :=
  (abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_degreewise
    cut
    complex
    hdegree
    probe
    degree).exact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
