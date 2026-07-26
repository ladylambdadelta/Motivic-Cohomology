import Mathlib.Algebra.Homology.ShortComplex.Exact
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Support.EpiMono.Owner

/-!
# Intrinsic probe-degree short-exact fields from supported isomorphisms

This file records the intrinsic abelian-envelope consequences of the supported
map identifications in the normalized truncation decomposition.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- On a normalized lower-tail degree, the intrinsic evaluated upper map is
zero because its target is zero. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_g_zero_of_lowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).g =
      0 :=
  (TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_X₃_isZero_of_lowerTail
      cut
      complex
      probe
      lowerTail).eq_of_tgt
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).g
        0

/-- Off the paired lower tail, the intrinsic evaluated lower map is zero
because its source is zero. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_f_zero_of_lowerTail_none
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f =
      0 :=
  (TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_X₁_isZero_of_lowerTail_none
      cut
      complex
      probe
      degree
      hnone).eq_of_src
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).f
        0

/-- A lower-tail isomorphism of the intrinsic first evaluated map gives
lower-tail exactness. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_exact_of_lowerTail_isIso_f
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ)
    (hiso :
      IsIso
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).f) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).Exact :=
  letI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).f :=
    hiso
  letI :
      Epi
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).f :=
    inferInstance
  ((TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).exact_iff_epi
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_g_zero_of_lowerTail
        cut
        complex
        probe
        lowerTail)).mpr
    inferInstance

/-- A lower-tail isomorphism of the intrinsic first evaluated map gives
lower-tail monicity. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_mono_f_of_lowerTail_isIso_f
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ)
    (hiso :
      IsIso
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).f) :
    Mono
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).f :=
  letI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).f :=
    hiso
  inferInstance

/-- An off-lower-tail isomorphism of the intrinsic second evaluated map gives
off-lower-tail exactness. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_exact_of_lowerTail_none_isIso_g
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hiso :
      IsIso
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).g) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).Exact :=
  letI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).g :=
    hiso
  letI :
      Mono
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).g :=
    inferInstance
  ((TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).exact_iff_mono
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_f_zero_of_lowerTail_none
        cut
        complex
        probe
        degree
        hnone)).mpr
    inferInstance

/-- An off-lower-tail isomorphism of the intrinsic second evaluated map gives
off-lower-tail epicity. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_epi_g_of_lowerTail_none_isIso_g
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (_hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hiso :
      IsIso
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).g) :
    Epi
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g :=
  letI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).g :=
    hiso
  inferInstance

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
