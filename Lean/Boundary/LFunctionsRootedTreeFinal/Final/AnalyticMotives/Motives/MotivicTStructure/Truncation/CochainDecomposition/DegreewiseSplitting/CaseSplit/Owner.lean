import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.ShortComplex.Owner

/-!
# Degreewise splitting by lower-tail case split

This file gives the concrete case split needed to construct degreewise
splittings for the normalized cochain truncation-decomposition short complex.
The two cases match the existing exactness proof: a degree either lies in the
paired lower tail or it lies outside that tail.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise splitting of the normalized cochain-decomposition short complex
follows by splitting a degree according to the paired lower-tail embedding. -/
theorem additiveCochainDecompositionDegreewiseSplitting_of_lowerTail_or_offLowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hlower :
      ∀ lowerTail : ℕ,
        ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveCategoryObject
            (ComplexShape.up ℤ)
            (cut - 1 - (lowerTail : ℤ)))).Splitting)
    (hoff :
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
            degree)).Splitting)
    (degree : ℤ) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        degree)).Splitting :=
  match htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
          degree with
  | none =>
      hoff degree htail
  | some lowerTail =>
      let hdegree :
          TraceAnalyticMotivicTStructure.decompositionLowerCut cut -
              (lowerTail : ℤ) =
            degree :=
        ComplexShape.Embedding.f_eq_of_r_eq_some
          (e :=
            TraceAnalyticMotivicTStructure.truncLEEmbedding
              (TraceAnalyticMotivicTStructure.decompositionLowerCut cut))
          htail
      match hdegree with
      | rfl =>
          hlower lowerTail

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
