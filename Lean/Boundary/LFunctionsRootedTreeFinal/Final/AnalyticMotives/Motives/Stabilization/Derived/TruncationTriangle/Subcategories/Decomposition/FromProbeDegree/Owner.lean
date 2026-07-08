import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.FromProbeDegree.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Subcategories.Decomposition.Owner

/-!
# Homological-subcategory truncation decomposition from probe-degree exactness

This file gives the direct probe-degree entry point for the derived truncation
triangle whose first and third vertices are exposed as aisle and coaisle
objects.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The lower aisle vertex obtained from concrete probe-degree lower-tail and
off-tail exactness data. -/
def abelianEnvelopeCochainDecompositionDerivedLowerAisleObjectOfProbeDegreeCasewise
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
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut) :=
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangleLowerAisleObject
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExactFromProbeDegreeCasewise
          cut
          complex
          hasHomology
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

/-- The upper coaisle vertex obtained from concrete probe-degree lower-tail and
off-tail exactness data. -/
def abelianEnvelopeCochainDecompositionDerivedUpperCoaisleObjectOfProbeDegreeCasewise
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
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle cut :=
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangleUpperCoaisleObject
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExactFromProbeDegreeCasewise
          cut
          complex
          hasHomology
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

/-- The subcategory-exposed truncation triangle obtained directly from
concrete probe-degree lower-tail and off-tail exactness data. -/
def abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangleOfProbeDegreeCasewise
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
    Triangle TraceAnalyticDerivedMotiveCategory :=
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangle
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExactFromProbeDegreeCasewise
          cut
          complex
          hasHomology
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

/-- Probe-degree exactness gives a distinguished derived analytic truncation
triangle whose first and third vertices are exposed through the aisle and
coaisle inclusions. -/
theorem abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangleOfProbeDegreeCasewise_distinguished
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
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangleOfProbeDegreeCasewise
          cut
          complex
          hasHomology
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi ∈
      distTriang TraceAnalyticDerivedMotiveCategory :=
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangle_distinguished
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExactFromProbeDegreeCasewise
          cut
          complex
          hasHomology
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
