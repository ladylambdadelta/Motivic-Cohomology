import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.IsIso.Owner

/-!
# Exactness from equality with an evaluated isomorphism hom

The nonboundary truncation formulas identify evaluated maps with homs of
explicit `ModuleCat Rat` isomorphisms.  This file turns such an equality into
the corresponding evaluated exactness statement.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- A `ModuleCat Rat` map equal to the hom of an isomorphism is an isomorphism. -/
theorem moduleCat_isIso_of_eq_iso_hom
    {source target : ModuleCat Rat}
    (map : source ⟶ target)
    (iso : source ≅ target)
    (hmap : map = iso.hom) :
    IsIso map :=
  Eq.ndrec
    (motive := fun hom => IsIso hom)
    (inferInstance : IsIso iso.hom)
    hmap.symm

/-- On a normalized lower-tail degree, equality of the first evaluated map
with the hom of a `ModuleCat Rat` isomorphism proves exactness. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeLowerTailExact_of_f_eq_iso_hom
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ)
    (iso :
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).X₁ ≅
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).X₂)
    (hmap :
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).f =
        iso.hom) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      (cut - 1 - (lowerTail : ℤ))).Exact :=
  letI :
      IsIso
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).f :=
    TraceAnalyticMotivicTStructure.moduleCat_isIso_of_eq_iso_hom
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).f
      iso
      hmap
  TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeLowerTailExact_of_isIso_f
    cut
    complex
    probe
    lowerTail

/-- Outside the paired lower-tail embedding, equality of the second evaluated
map with the hom of a `ModuleCat Rat` isomorphism proves exactness. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailExact_of_g_eq_iso_hom
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (iso :
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).X₂ ≅
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).X₃)
    (hmap :
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g =
        iso.hom) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  letI :
      IsIso
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g :=
    TraceAnalyticMotivicTStructure.moduleCat_isIso_of_eq_iso_hom
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g
      iso
      hmap
  TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailExact_of_isIso_g
    cut
    complex
    probe
    degree
    hnone

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
