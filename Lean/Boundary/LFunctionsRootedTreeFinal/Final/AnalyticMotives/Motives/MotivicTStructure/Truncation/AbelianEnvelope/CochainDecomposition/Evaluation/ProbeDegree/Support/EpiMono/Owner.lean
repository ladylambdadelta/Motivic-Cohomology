import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Support.LowerInclusion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Support.UpperProjection.Owner

/-!
# Intrinsic probe-degree mono and epi from support

This file turns the intrinsic abelian-envelope support vanishing statements
into the mono and epi side fields needed in the evaluated short-exact
case split.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- Off the lower-tail embedding, the first object of the intrinsic evaluated
truncation short complex is zero. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_X₁_isZero_of_lowerTail_none
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none) :
    IsZero
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).X₁ :=
  (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe).map_isZero
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLE_X_isZero_of_r_eq_none
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
        complex
        degree
        hnone)

/-- Off the lower-tail embedding, the first map of the intrinsic evaluated
truncation short complex is monic because its source is zero. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_mono_f_of_lowerTail_none
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none) :
    Mono
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).f :=
  mono_of_source_iso_zero
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f
    (IsZero.iso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_X₁_isZero_of_lowerTail_none
          cut
          complex
          probe
          degree
          hnone)
      (show IsZero (0 : ModuleCat Rat) from isZero_zero))

/-- On a normalized lower-tail degree, the third object of the intrinsic
evaluated truncation short complex is zero. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_X₃_isZero_of_lowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ) :
    IsZero
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).X₃ :=
  (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe).map_isZero
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGE_X_isZero_of_decompositionLowerTail
        cut
        complex
        lowerTail)

/-- On a normalized lower-tail degree, the second map of the intrinsic
evaluated truncation short complex is epic because its target is zero. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_epi_g_of_lowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ) :
    Epi
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).g :=
  epi_of_target_iso_zero
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).g
    (IsZero.iso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_X₃_isZero_of_lowerTail
          cut
          complex
          probe
          lowerTail)
      (show IsZero (0 : ModuleCat Rat) from isZero_zero))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
