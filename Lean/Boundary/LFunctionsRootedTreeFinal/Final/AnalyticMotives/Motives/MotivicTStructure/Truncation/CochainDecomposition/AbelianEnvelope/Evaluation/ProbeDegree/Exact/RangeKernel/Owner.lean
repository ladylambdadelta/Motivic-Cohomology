import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Maps.Owner

/-!
# Range-kernel exactness criterion for evaluated truncation short complexes

This file specializes the module-category exactness criterion to the concrete
Q-module short complex obtained by evaluating the Yoneda truncation sequence at
one analytic probe and one cochain degree.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Exactness of the evaluated Q-module truncation short complex is equivalent
to equality between the range of the first evaluated map and the kernel of the
second evaluated map. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeExact_iff_range_eq_ker
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact ↔
      LinearMap.range
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).f =
        LinearMap.ker
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).g :=
  ShortComplex.moduleCat_exact_iff_range_eq_ker
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree)

/-- A range-kernel equality proves exactness of the evaluated Q-module
truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeExact_of_range_eq_ker
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hrange :
      LinearMap.range
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).f =
        LinearMap.ker
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).g) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeExact_iff_range_eq_ker
    cut
    complex
    probe
    degree).mpr
      hrange

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
