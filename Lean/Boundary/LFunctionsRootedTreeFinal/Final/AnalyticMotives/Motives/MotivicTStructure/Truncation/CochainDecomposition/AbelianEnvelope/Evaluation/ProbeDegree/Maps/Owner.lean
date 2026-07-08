import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Owner

/-!
# Maps in the probe-degree truncation short complex

This file exposes the two maps of the evaluated Q-module short complex as the
probe evaluation of the Yoneda images of the concrete lower inclusion and
upper projection.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The first map of the evaluated truncation short complex is the probe
evaluation of the Yoneda image of the concrete lower-inclusion component. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).f =
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionLowerMap
          cut
          complex).f degree)).app
        (Opposite.op probe) :=
  rfl

/-- The second map of the evaluated truncation short complex is the probe
evaluation of the Yoneda image of the concrete upper-projection component. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).g =
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionUpperMap
          cut
          complex).f degree)).app
        (Opposite.op probe) :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
