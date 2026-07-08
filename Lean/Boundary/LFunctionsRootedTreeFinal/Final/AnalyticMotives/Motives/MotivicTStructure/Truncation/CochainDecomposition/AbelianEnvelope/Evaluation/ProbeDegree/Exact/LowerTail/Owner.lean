import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.RangeKernel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Support.UpperProjection.Owner

/-!
# Lower-tail exactness reduction for evaluated truncation short complexes

On a normalized lower-tail degree, the evaluated upper projection is zero.
Exactness at such a degree therefore reduces to surjectivity of the evaluated
lower inclusion.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If an evaluated Q-linear map is zero, its kernel is the top submodule. -/
theorem linearMap_ker_eq_top_of_eq_zero
    {source target : ModuleCat Rat}
    (map : source ⟶ target)
    (hmap : map = 0) :
    LinearMap.ker map =
      ⊤ :=
  (LinearMap.ker_eq_top).mpr hmap

/-- On a normalized lower-tail degree, exactness of the evaluated truncation
short complex follows from the first evaluated map having full range. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeLowerTailExact_of_range_top
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ)
    (hrange :
      LinearMap.range
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).f =
        ⊤) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      (cut - 1 - (lowerTail : ℤ))).Exact :=
  TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeExact_of_range_eq_ker
    cut
    complex
    probe
    (cut - 1 - (lowerTail : ℤ))
    (Eq.trans
      hrange
      (Eq.symm
        (TraceAnalyticMotivicTStructure.linearMap_ker_eq_top_of_eq_zero
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).g
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_g_of_lowerTail
            cut
            complex
            probe
            lowerTail))))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
