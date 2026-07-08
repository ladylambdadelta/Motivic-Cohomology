import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Owner

/-!
# Maps in the intrinsic probe-degree truncation short complex

This file exposes the two maps of the evaluated Q-module short complex as the
probe-degree components of the intrinsic abelian-envelope lower inclusion and
upper projection.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The first map of the intrinsic evaluated truncation short complex is the
probe-degree component of the abelian-envelope lower-inclusion map. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f =
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionLowerMap cut complex).f
          degree).app
        (Opposite.op probe) :=
  rfl

/-- The second map of the intrinsic evaluated truncation short complex is the
probe-degree component of the abelian-envelope upper-projection map. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g =
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionUpperMap cut complex).f
          degree).app
        (Opposite.op probe) :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
