import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.Constructors.ProbeDegreeCasewise.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.FieldShape.Owner

/-!
# Probe-degree constructor for field-order truncation existence

This file composes the probe-degree analytic constructor for
`HasYonedaTruncationRepresentative` with the field-order truncation theorem.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Probe-degree analytic data at an arbitrary cut gives the exact field-order
truncation triangle for the represented derived object. -/
theorem probeDegreeCasewise_exists_object_truncation_triangle_fieldShape
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).g) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ :
        TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper)
      (firstMap :
        lower ⟶
          TraceAnalyticDerivedMotiveCategory.objectOf
            (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex))
      (secondMap :
        TraceAnalyticDerivedMotiveCategory.objectOf
            (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex) ⟶
          upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentative_exists_object_truncation_triangle_fieldShape
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex))
      (TraceAnalyticMotivicTStructure
        .hasYonedaTruncationRepresentativeOfProbeDegreeCasewise
          cut
          complex
          hasHomology
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

/-- Probe-degree analytic data at cut `1` gives the exact field-order
truncation triangle for the represented derived object. -/
theorem probeDegreeCasewise_exists_triangle_zero_one_fieldShape
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              1
              complex
              probe
              (1 - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                1
                complex
                probe
                (1 - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              1
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                1
                complex
                probe
                degree).g) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap :
        lower ⟶
          TraceAnalyticDerivedMotiveCategory.objectOf
            (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex))
      (secondMap :
        TraceAnalyticDerivedMotiveCategory.objectOf
            (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex) ⟶
          upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .probeDegreeCasewise_exists_object_truncation_triangle_fieldShape
      1
      complex
      hasHomology
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
