import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.LowerTail.ZeroUpper.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.OffLowerTail.ZeroLower.Owner

/-!
# Degreewise splitting assembly for the normalized cochain decomposition

This file combines the lower-tail and off-lower-tail splitting reductions into
one concrete degreewise splitting family for the normalized cochain
truncation-decomposition short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise splittings of the normalized cochain-decomposition short complex
assemble from explicit lower-tail inverses for the lower map and explicit
off-lower-tail inverses for the upper map. -/
theorem additiveCochainDecompositionDegreewiseSplitting_of_local_twoSidedInverses
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
        degree)).Splitting :=
  TraceAnalyticMotivicTStructure
    .additiveCochainDecompositionDegreewiseSplitting_of_lowerTail_or_offLowerTail
      cut
      complex
      (fun lowerTail =>
        TraceAnalyticMotivicTStructure
          .additiveCochainDecompositionLowerTailSplitting_of_lowerMap_twoSidedInverse
            cut
            complex
            lowerTail
            (lowerInverse lowerTail)
            (lower_f_r lowerTail)
            (lower_r_f lowerTail))
      (fun degree hnone =>
        TraceAnalyticMotivicTStructure
          .additiveCochainDecompositionOffLowerTailSplitting_of_upperMap_twoSidedInverse
            cut
            complex
            degree
            hnone
            (upperInverse degree hnone)
            (upper_s_g degree hnone)
            (upper_g_s degree hnone))
      degree

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
