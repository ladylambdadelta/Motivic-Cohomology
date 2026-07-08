import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.LowerInclusion.Owner

/-!
# Evaluated lower-inclusion support

This file lifts the concrete lower-inclusion support theorem through Yoneda
and probe-degree evaluation.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Outside the paired lower-tail embedding, the first map of the evaluated
truncation short complex is zero. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_f_of_lowerTail_none
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).f =
      0 :=
  Eq.trans
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_f
      cut
      complex
      probe
      degree)
    (Eq.trans
      (congrArg
        (fun component =>
          ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map component).app
            (Opposite.op probe))
        (TraceAnalyticMotivicTStructure.additiveTruncLEInclusionMap_f_of_r_eq_none
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          complex
          degree
          hnone))
      (congrArg
        (fun naturalTransformation =>
          naturalTransformation.app (Opposite.op probe))
        (Functor.map_zero
          TraceAnalyticAdditiveAbelianEnvelope.yoneda
          ((TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
            cut
            complex).X degree)
          (complex.X degree))))

/-- Outside the paired lower-tail embedding, the first object of the evaluated
truncation short complex is zero. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_X₁_isZero_of_lowerTail_none
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none) :
    CategoryTheory.Limits.IsZero
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).X₁ :=
  (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe).map_isZero
    ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map_isZero
      (TraceAnalyticMotivicTStructure.additiveTruncLE_X_isZero_of_r_eq_none
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
        complex
        degree
        hnone))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
