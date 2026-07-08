import Mathlib.Algebra.Homology.Embedding.IsSupported
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.LowerInclusion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Support.LowerInclusion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Support.Cut.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Owner

/-!
# Bounds for the derived analytic truncation triangle vertices

This file proves that the concrete abelian-envelope truncation complexes used
as the first and third vertices of the derived truncation triangle satisfy the
expected homological bounds after quasi-isomorphism localization.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The concrete additive upper truncation is strictly supported on the
upper-tail embedding. -/
theorem additiveTruncGE_isStrictlySupported
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveTruncGE
      cut
      complex).IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut) where
  isZero degree hdegree :=
    show
        IsZero
          (((complex.truncGE'
            (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)).extend
              (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)).X
            degree) from
      ((complex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)).isZero_extend_X
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
          degree
          hdegree)

/-- The concrete additive lower truncation is strictly supported on the
lower-tail embedding. -/
theorem additiveTruncLE_isStrictlySupported
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveTruncLE
      cut
      complex).IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding cut) where
  isZero degree hdegree :=
    TraceAnalyticMotivicTStructure
      .additiveTruncLE_X_isZero_of_r_eq_none
        cut
        complex
        degree
        ((TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r_eq_none
          degree
          hdegree)

/-- The Yoneda image of the concrete additive upper truncation is strictly
supported on the upper-tail embedding. -/
theorem yonedaCochainComplex_additiveTruncGE_isStrictlySupported
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
      (TraceAnalyticMotivicTStructure.additiveTruncGE
        cut
        complex)).IsStrictlySupported
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut) :=
  letI :
      (TraceAnalyticMotivicTStructure.additiveTruncGE
        cut
        complex).IsStrictlySupported
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut) :=
    TraceAnalyticMotivicTStructure
      .additiveTruncGE_isStrictlySupported cut complex
  inferInstance

/-- The Yoneda image of the concrete additive lower truncation is strictly
supported on the lower-tail embedding. -/
theorem yonedaCochainComplex_additiveTruncLE_isStrictlySupported
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
      (TraceAnalyticMotivicTStructure.additiveTruncLE
        cut
        complex)).IsStrictlySupported
          (TraceAnalyticMotivicTStructure.truncLEEmbedding cut) :=
  letI :
      (TraceAnalyticMotivicTStructure.additiveTruncLE
        cut
        complex).IsStrictlySupported
          (TraceAnalyticMotivicTStructure.truncLEEmbedding cut) :=
    TraceAnalyticMotivicTStructure
      .additiveTruncLE_isStrictlySupported cut complex
  inferInstance

/-- The represented concrete additive upper truncation gives a derived object
homologically `≥ cut`. -/
theorem yonedaCochainComplex_additiveTruncGE_derived_homologicalGE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
          (TraceAnalyticMotivicTStructure.additiveTruncGE
            cut
            complex))) :=
  letI :
      (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
        (TraceAnalyticMotivicTStructure.additiveTruncGE
          cut
          complex)).IsStrictlySupported
            (TraceAnalyticMotivicTStructure.truncGEEmbedding cut) :=
    TraceAnalyticMotivicTStructure
      .yonedaCochainComplex_additiveTruncGE_isStrictlySupported
        cut
        complex
  TraceAnalyticDerivedMotiveCategory
    .homologicalGE_objectOf_of_truncGEEmbedding_isSupported
      cut
      (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
        (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex))

/-- The represented concrete additive lower truncation gives a derived object
homologically `≤ cut`. -/
theorem yonedaCochainComplex_additiveTruncLE_derived_homologicalLE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
          (TraceAnalyticMotivicTStructure.additiveTruncLE
            cut
            complex))) :=
  letI :
      (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
        (TraceAnalyticMotivicTStructure.additiveTruncLE
          cut
          complex)).IsStrictlySupported
            (TraceAnalyticMotivicTStructure.truncLEEmbedding cut) :=
    TraceAnalyticMotivicTStructure
      .yonedaCochainComplex_additiveTruncLE_isStrictlySupported
        cut
        complex
  TraceAnalyticDerivedMotiveCategory
    .homologicalLE_objectOf_of_truncLEEmbedding_isSupported
      cut
      (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
        (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex))

/-- The represented concrete lower truncation used in the normalized
decomposition gives a derived object homologically `≤ cut - 1`. -/
theorem yonedaCochainComplex_additiveDecompositionTruncLE_derived_homologicalLE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
            cut
            complex))) :=
  TraceAnalyticMotivicTStructure
    .yonedaCochainComplex_additiveTruncLE_derived_homologicalLE
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
      complex

/-- The abelian-envelope upper truncation is strictly supported on the concrete
upper-tail embedding. -/
theorem abelianEnvelopeTruncGE_isStrictlySupported
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE
      cut
      complex).IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut) where
  isZero degree hdegree :=
    letI : ∀ degree : ℤ, complex.HasHomology degree :=
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainComplex_hasHomology_all complex
    show
        IsZero
          (((complex.truncGE'
            (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)).extend
              (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)).X
            degree) from
      ((complex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)).isZero_extend_X
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
          degree
          hdegree)

/-- The abelian-envelope lower truncation is strictly supported on the concrete
lower-tail embedding. -/
theorem abelianEnvelopeTruncLE_isStrictlySupported
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE
      cut
      complex).IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding cut) where
  isZero degree hdegree :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLE_X_isZero_of_r_eq_none
        cut
        complex
        degree
        ((TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r_eq_none
          degree
          hdegree)

/-- The upper vertex of the derived truncation triangle is homologically
`≥ cut`. -/
theorem abelianEnvelopeTruncGE_derived_homologicalGE
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE
          cut
          complex)) :=
  letI :
      (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE
        cut
        complex).IsStrictlySupported
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut) :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGE_isStrictlySupported cut complex
  TraceAnalyticDerivedMotiveCategory
    .homologicalGE_objectOf_of_truncGEEmbedding_isSupported
      cut
      (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex)

/-- The lower vertex of the derived truncation triangle is homologically
`≤ cut`. -/
theorem abelianEnvelopeTruncLE_derived_homologicalLE
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE
          cut
          complex)) :=
  letI :
      (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE
        cut
        complex).IsStrictlySupported
          (TraceAnalyticMotivicTStructure.truncLEEmbedding cut) :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLE_isStrictlySupported cut complex
  TraceAnalyticDerivedMotiveCategory
    .homologicalLE_objectOf_of_truncLEEmbedding_isSupported
      cut
      (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE cut complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
