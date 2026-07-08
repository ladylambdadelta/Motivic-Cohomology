import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.CollectiveEvaluation.Exact.Coordinates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Exact.ProbeDegree.IsIso.Owner

/-!
# Degreewise exactness from probe-degree exactness

This file assembles exactness of the degreewise abelian-envelope truncation
short complex from exactness after every analytic additive probe evaluation.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If every named probe-degree Q-module truncation short complex is exact,
then each degreewise abelian-envelope truncation short complex is exact. -/
theorem abelianEnvelopeCochainDecompositionDegreeExact_of_probeDegreeExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hprobe :
      ∀ (probe : TraceAnalyticAdditiveCategoryObject) (degree : ℤ),
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).Exact)
    (degree : ℤ) :
    ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree)).Exact :=
  TraceAnalyticAdditiveAbelianEnvelope.exact_of_evaluation_exact
    ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree))
    (fun probe => hprobe probe degree)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
