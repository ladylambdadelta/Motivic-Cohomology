import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.UpperProjection.Owner

/-!
# Evaluated upper-projection support

This file lifts the concrete upper-projection support theorem through Yoneda
and probe-degree evaluation.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- On a normalized lower-tail degree, the second map of the evaluated
truncation short complex is zero. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_g_of_lowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      (cut - 1 - (lowerTail : ℤ))).g =
      0 :=
  Eq.trans
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_g
      cut
      complex
      probe
      (cut - 1 - (lowerTail : ℤ)))
    (Eq.trans
      (congrArg
        (fun component =>
          ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map component).app
            (Opposite.op probe))
        (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap_f_of_decompositionLowerTail
          cut
          complex
          lowerTail))
      (congrArg
        (fun naturalTransformation =>
          naturalTransformation.app (Opposite.op probe))
        (Functor.map_zero
          TraceAnalyticAdditiveAbelianEnvelope.yoneda
          (complex.X (cut - 1 - (lowerTail : ℤ)))
          ((TraceAnalyticMotivicTStructure.additiveTruncGE
            cut
            complex).X (cut - 1 - (lowerTail : ℤ))))))

/-- On a normalized lower-tail degree, the third object of the evaluated
truncation short complex is zero. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_X₃_isZero_of_lowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ) :
    CategoryTheory.Limits.IsZero
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).X₃ :=
  (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe).map_isZero
    ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map_isZero
      (TraceAnalyticMotivicTStructure.additiveTruncGE_X_isZero_of_decompositionLowerTail
        cut
        complex
        lowerTail))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
