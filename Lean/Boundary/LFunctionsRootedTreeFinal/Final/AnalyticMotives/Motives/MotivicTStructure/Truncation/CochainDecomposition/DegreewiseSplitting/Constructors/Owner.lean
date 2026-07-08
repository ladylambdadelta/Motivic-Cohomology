import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.ShortExact.Owner

/-!
# Constructor surface for degreewise splitting fields

This file composes the local two-sided-inverse splitting assembly theorem with
the exact, mono, epi, and short-exact field extractors for split short
complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Local lower-tail and off-lower-tail two-sided inverse data give
degreewise exactness of the normalized cochain-decomposition short complex. -/
theorem additiveCochainDecompositionDegreewiseExact_of_local_twoSidedInverses
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerInverse :
      ∀ lowerTail : ℕ,
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            (cut - 1 - (lowerTail : ℤ)))).X₂ ⟶
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              (cut - 1 - (lowerTail : ℤ)))).X₁)
    (lower_f_r :
      ∀ lowerTail : ℕ,
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            (cut - 1 - (lowerTail : ℤ)))).f ≫ lowerInverse lowerTail =
          𝟙 _)
    (lower_r_f :
      ∀ lowerTail : ℕ,
        lowerInverse lowerTail ≫
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              (cut - 1 - (lowerTail : ℤ)))).f =
          𝟙 _)
    (upperInverse :
      ∀ degree : ℤ,
        (TraceAnalyticMotivicTStructure.truncLEEmbedding
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
          none →
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            degree)).X₃ ⟶
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              degree)).X₂)
    (upper_s_g :
      ∀ (degree : ℤ)
        (hnone :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none),
        upperInverse degree hnone ≫
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              degree)).g =
          𝟙 _)
    (upper_g_s :
      ∀ (degree : ℤ)
        (hnone :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none),
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            degree)).g ≫ upperInverse degree hnone =
          𝟙 _)
    (degree : ℤ) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        degree)).Exact :=
  TraceAnalyticMotivicTStructure
    .additiveCochainDecompositionDegreewiseExact_of_splitting
      cut
      complex
      degree
      (TraceAnalyticMotivicTStructure
        .additiveCochainDecompositionDegreewiseSplitting_of_local_twoSidedInverses
          cut
          complex
          lowerInverse
          lower_f_r
          lower_r_f
          upperInverse
          upper_s_g
          upper_g_s
          degree)

/-- Local lower-tail and off-lower-tail two-sided inverse data make the
degreewise lower map monic in the normalized cochain-decomposition short
complex. -/
theorem additiveCochainDecompositionDegreewiseMono_f_of_local_twoSidedInverses
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerInverse :
      ∀ lowerTail : ℕ,
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            (cut - 1 - (lowerTail : ℤ)))).X₂ ⟶
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              (cut - 1 - (lowerTail : ℤ)))).X₁)
    (lower_f_r :
      ∀ lowerTail : ℕ,
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            (cut - 1 - (lowerTail : ℤ)))).f ≫ lowerInverse lowerTail =
          𝟙 _)
    (lower_r_f :
      ∀ lowerTail : ℕ,
        lowerInverse lowerTail ≫
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              (cut - 1 - (lowerTail : ℤ)))).f =
          𝟙 _)
    (upperInverse :
      ∀ degree : ℤ,
        (TraceAnalyticMotivicTStructure.truncLEEmbedding
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
          none →
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            degree)).X₃ ⟶
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              degree)).X₂)
    (upper_s_g :
      ∀ (degree : ℤ)
        (hnone :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none),
        upperInverse degree hnone ≫
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              degree)).g =
          𝟙 _)
    (upper_g_s :
      ∀ (degree : ℤ)
        (hnone :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none),
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            degree)).g ≫ upperInverse degree hnone =
          𝟙 _)
    (degree : ℤ) :
    Mono
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).f :=
  TraceAnalyticMotivicTStructure
    .additiveCochainDecompositionDegreewiseMono_f_of_splitting
      cut
      complex
      degree
      (TraceAnalyticMotivicTStructure
        .additiveCochainDecompositionDegreewiseSplitting_of_local_twoSidedInverses
          cut
          complex
          lowerInverse
          lower_f_r
          lower_r_f
          upperInverse
          upper_s_g
          upper_g_s
          degree)

/-- Local lower-tail and off-lower-tail two-sided inverse data make the
degreewise upper map epic in the normalized cochain-decomposition short
complex. -/
theorem additiveCochainDecompositionDegreewiseEpi_g_of_local_twoSidedInverses
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerInverse :
      ∀ lowerTail : ℕ,
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            (cut - 1 - (lowerTail : ℤ)))).X₂ ⟶
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              (cut - 1 - (lowerTail : ℤ)))).X₁)
    (lower_f_r :
      ∀ lowerTail : ℕ,
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            (cut - 1 - (lowerTail : ℤ)))).f ≫ lowerInverse lowerTail =
          𝟙 _)
    (lower_r_f :
      ∀ lowerTail : ℕ,
        lowerInverse lowerTail ≫
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              (cut - 1 - (lowerTail : ℤ)))).f =
          𝟙 _)
    (upperInverse :
      ∀ degree : ℤ,
        (TraceAnalyticMotivicTStructure.truncLEEmbedding
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
          none →
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            degree)).X₃ ⟶
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              degree)).X₂)
    (upper_s_g :
      ∀ (degree : ℤ)
        (hnone :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none),
        upperInverse degree hnone ≫
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              degree)).g =
          𝟙 _)
    (upper_g_s :
      ∀ (degree : ℤ)
        (hnone :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none),
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            degree)).g ≫ upperInverse degree hnone =
          𝟙 _)
    (degree : ℤ) :
    Epi
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).g :=
  TraceAnalyticMotivicTStructure
    .additiveCochainDecompositionDegreewiseEpi_g_of_splitting
      cut
      complex
      degree
      (TraceAnalyticMotivicTStructure
        .additiveCochainDecompositionDegreewiseSplitting_of_local_twoSidedInverses
          cut
          complex
          lowerInverse
          lower_f_r
          lower_r_f
          upperInverse
          upper_s_g
          upper_g_s
          degree)

/-- Local lower-tail and off-lower-tail two-sided inverse data give
degreewise short exactness of the normalized cochain-decomposition short
complex. -/
theorem additiveCochainDecompositionDegreewiseShortExact_of_local_twoSidedInverses
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerInverse :
      ∀ lowerTail : ℕ,
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            (cut - 1 - (lowerTail : ℤ)))).X₂ ⟶
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              (cut - 1 - (lowerTail : ℤ)))).X₁)
    (lower_f_r :
      ∀ lowerTail : ℕ,
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            (cut - 1 - (lowerTail : ℤ)))).f ≫ lowerInverse lowerTail =
          𝟙 _)
    (lower_r_f :
      ∀ lowerTail : ℕ,
        lowerInverse lowerTail ≫
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              (cut - 1 - (lowerTail : ℤ)))).f =
          𝟙 _)
    (upperInverse :
      ∀ degree : ℤ,
        (TraceAnalyticMotivicTStructure.truncLEEmbedding
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
          none →
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            degree)).X₃ ⟶
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              degree)).X₂)
    (upper_s_g :
      ∀ (degree : ℤ)
        (hnone :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none),
        upperInverse degree hnone ≫
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveCategoryObject
              (ComplexShape.up ℤ)
              degree)).g =
          𝟙 _)
    (upper_g_s :
      ∀ (degree : ℤ)
        (hnone :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none),
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            degree)).g ≫ upperInverse degree hnone =
          𝟙 _)
    (degree : ℤ) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        degree)).ShortExact :=
  TraceAnalyticMotivicTStructure
    .additiveCochainDecompositionDegreewiseShortExact_of_splitting
      cut
      complex
      degree
      (TraceAnalyticMotivicTStructure
        .additiveCochainDecompositionDegreewiseSplitting_of_local_twoSidedInverses
          cut
          complex
          lowerInverse
          lower_f_r
          lower_r_f
          upperInverse
          upper_s_g
          upper_g_s
          degree)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
