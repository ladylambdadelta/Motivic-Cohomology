import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.LowerInclusion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.UpperProjection.Owner

/-!
# Composite zero for the normalized cochain truncation decomposition

This file proves the cochain-level identity
`truncLE(cut - 1, K) ⟶ K ⟶ truncGE(cut, K)` is zero.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise zero of the normalized lower-inclusion/upper-projection
composite. -/
theorem additiveCochainDecompositionCompositeMap_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.additiveCochainDecompositionCompositeMap
        cut
        complex).f degree =
      0 :=
  match htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
          degree with
  | none =>
      let lowerZero :
          (TraceAnalyticMotivicTStructure.additiveCochainDecompositionLowerMap
            cut
            complex).f degree =
            0 :=
        TraceAnalyticMotivicTStructure.additiveTruncLEInclusionMap_f_of_r_eq_none
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          complex
          degree
          htail
      Eq.trans
        (congrArg
          (fun lowerComponent =>
            lowerComponent ≫
              (TraceAnalyticMotivicTStructure.additiveCochainDecompositionUpperMap
                cut
                complex).f degree)
          lowerZero)
        (zero_comp
          ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionUpperMap
            cut
            complex).f degree))
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
          let upperZero :
              (TraceAnalyticMotivicTStructure.additiveCochainDecompositionUpperMap
                cut
                complex).f
                  (TraceAnalyticMotivicTStructure.decompositionLowerCut cut -
                    (lowerTail : ℤ)) =
                0 :=
            TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap_f_of_decompositionLowerTail
              cut
              complex
              lowerTail
          Eq.trans
            (congrArg
              (fun upperComponent =>
                (TraceAnalyticMotivicTStructure.additiveCochainDecompositionLowerMap
                  cut
                  complex).f
                    (TraceAnalyticMotivicTStructure.decompositionLowerCut cut -
                      (lowerTail : ℤ)) ≫
                  upperComponent)
              upperZero)
            (comp_zero
              ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionLowerMap
                cut
                complex).f
                  (TraceAnalyticMotivicTStructure.decompositionLowerCut cut -
                    (lowerTail : ℤ))))

/-- The normalized cochain truncation decomposition has zero composite. -/
theorem additiveCochainDecompositionCompositeMap_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveCochainDecompositionCompositeMap
        cut
        complex =
      0 :=
  HomologicalComplex.hom_ext
    (TraceAnalyticMotivicTStructure.additiveCochainDecompositionCompositeMap
      cut
      complex)
    0
    (TraceAnalyticMotivicTStructure.additiveCochainDecompositionCompositeMap_f
      cut
      complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
