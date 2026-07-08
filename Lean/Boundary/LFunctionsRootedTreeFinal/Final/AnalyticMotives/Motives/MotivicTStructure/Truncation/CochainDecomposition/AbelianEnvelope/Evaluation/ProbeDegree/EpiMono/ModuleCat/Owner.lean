import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.EpiMono.Owner

/-!
# Q-module mono and epi criteria for probe-degree truncation maps

This file connects ordinary injectivity and surjectivity of the concrete
`ModuleCat Rat` maps to categorical monomorphisms and epimorphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- A morphism of Q-modules whose source is a zero object is monic. -/
theorem moduleCat_mono_of_isZero_source
    {source target : ModuleCat Rat}
    (hsource : CategoryTheory.Limits.IsZero source)
    (map : source ⟶ target) :
    Mono map where
  right_cancellation := fun _ left right _ =>
    hsource.eq_of_tgt left right

/-- A morphism of Q-modules whose target is a zero object is epic. -/
theorem moduleCat_epi_of_isZero_target
    {source target : ModuleCat Rat}
    (htarget : CategoryTheory.Limits.IsZero target)
    (map : source ⟶ target) :
    Epi map where
  left_cancellation := fun _ left right _ =>
    htarget.eq_of_src left right

/-- An injective morphism of `ModuleCat Rat` objects is monic. -/
theorem moduleCat_mono_of_injective
    {source target : ModuleCat Rat}
    (map : source ⟶ target)
    (hinjective : Function.Injective map) :
    Mono map :=
  (ModuleCat.mono_iff_injective map).mpr hinjective

/-- A surjective morphism of `ModuleCat Rat` objects is epic. -/
theorem moduleCat_epi_of_surjective
    {source target : ModuleCat Rat}
    (map : source ⟶ target)
    (hsurjective : Function.Surjective map) :
    Epi map :=
  (ModuleCat.epi_iff_surjective map).mpr hsurjective

/-- An isomorphism of `ModuleCat Rat` objects is monic. -/
theorem moduleCat_mono_of_isIso
    {source target : ModuleCat Rat}
    (map : source ⟶ target)
    [IsIso map] :
    Mono map :=
  inferInstance

/-- An isomorphism of `ModuleCat Rat` objects is epic. -/
theorem moduleCat_epi_of_isIso
    {source target : ModuleCat Rat}
    (map : source ⟶ target)
    [IsIso map] :
    Epi map :=
  inferInstance

/-- Injectivity of the first named probe-degree truncation map gives monicity
of that map. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeMono_f_of_injective
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hinjective :
      Function.Injective
        (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).f) :
    Mono
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).f :=
  moduleCat_mono_of_injective
    (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f
    hinjective

/-- Surjectivity of the second named probe-degree truncation map gives epicity
of that map. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeEpi_g_of_surjective
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hsurjective :
      Function.Surjective
        (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).g) :
    Epi
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g :=
  moduleCat_epi_of_surjective
    (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g
    hsurjective

/-- If the first named probe-degree truncation map is an isomorphism, then it
is monic. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeMono_f_of_isIso
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    [IsIso
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f] :
    Mono
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f :=
  moduleCat_mono_of_isIso
    (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).f

/-- If the second named probe-degree truncation map is an isomorphism, then it
is epic. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeEpi_g_of_isIso
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    [IsIso
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g] :
    Epi
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g :=
  moduleCat_epi_of_isIso
    (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).g

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
