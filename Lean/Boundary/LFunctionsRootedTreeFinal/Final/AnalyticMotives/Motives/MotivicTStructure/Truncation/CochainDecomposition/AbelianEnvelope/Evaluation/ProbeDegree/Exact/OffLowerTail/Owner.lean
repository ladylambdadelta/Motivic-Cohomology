import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.RangeKernel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Support.LowerInclusion.Owner

/-!
# Off-lower-tail exactness reduction for evaluated truncation short complexes

Outside the paired lower-tail embedding, the evaluated lower inclusion is zero.
Exactness at such a degree therefore reduces to injectivity of the evaluated
upper projection.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If an evaluated Q-linear map is zero, its range is the bottom submodule. -/
theorem linearMap_range_eq_bot_of_eq_zero
    {source target : ModuleCat Rat}
    (map : source ⟶ target)
    (hmap : map = 0) :
    LinearMap.range map =
      ⊥ :=
  (LinearMap.range_eq_bot).mpr hmap

/-- Outside the paired lower-tail embedding, exactness of the evaluated
truncation short complex follows from the second evaluated map having trivial
kernel. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailExact_of_ker_bot
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hker :
      LinearMap.ker
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).g =
        ⊥) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeExact_of_range_eq_ker
    cut
    complex
    probe
    degree
    (Eq.trans
      (TraceAnalyticMotivicTStructure.linearMap_range_eq_bot_of_eq_zero
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).f
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_f_of_lowerTail_none
          cut
          complex
          probe
          degree
          hnone))
      (Eq.symm hker))

/-- Outside the paired lower-tail embedding, exactness of the evaluated
truncation short complex forces the second evaluated map to have trivial
kernel. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTail_ker_bot_of_exact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hexact :
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).Exact) :
    LinearMap.ker
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g =
      ⊥ :=
  let range_eq_ker :
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
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeExact_iff_range_eq_ker
      cut
      complex
      probe
      degree).mp
      hexact
  let range_eq_bot :
      LinearMap.range
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).f =
        ⊥ :=
    TraceAnalyticMotivicTStructure.linearMap_range_eq_bot_of_eq_zero
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_f_of_lowerTail_none
        cut
        complex
        probe
        degree
        hnone)
  Eq.trans
    (Eq.symm range_eq_ker)
    range_eq_bot

/-- Outside the paired lower-tail embedding, objectwise exactness is
equivalent to trivial kernel of the evaluated upper projection. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailExact_iff_ker_bot
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
        degree).Exact ↔
      LinearMap.ker
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).g =
        ⊥ :=
  Iff.intro
    (fun hexact =>
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTail_ker_bot_of_exact
          cut
          complex
          probe
          degree
          hnone
          hexact)
    (fun hker =>
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailExact_of_ker_bot
          cut
          complex
          probe
          degree
          hnone
          hker)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
