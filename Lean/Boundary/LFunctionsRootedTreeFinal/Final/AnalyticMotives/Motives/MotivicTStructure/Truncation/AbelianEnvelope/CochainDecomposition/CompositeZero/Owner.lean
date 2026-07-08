import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Support.LowerInclusion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Support.UpperProjection.Owner

/-!
# Composite zero for abelian-envelope truncation decomposition

This file proves that the abelian-envelope normalized decomposition
`truncLE(cut - 1,K) ⟶ K ⟶ truncGE(cut,K)` has zero composite.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise zero of the abelian-envelope lower-inclusion/upper-projection
composite. -/
theorem abelianEnvelopeCochainDecompositionCompositeMap_f
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionCompositeMap cut complex).f
        degree =
      0 :=
  match htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
          degree with
  | none =>
      let lowerZero :
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionLowerMap
              cut
              complex).f degree =
            0 :=
        TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEInclusionMap_f_of_r_eq_none
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
            complex
            degree
            htail
      Eq.trans
        (congrArg
          (fun lowerComponent =>
            lowerComponent ≫
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeCochainDecompositionUpperMap
                  cut
                  complex).f degree)
          lowerZero)
        (zero_comp
          ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionUpperMap cut complex).f
              degree))
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
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeCochainDecompositionUpperMap
                  cut
                  complex).f
                  (TraceAnalyticMotivicTStructure.decompositionLowerCut cut -
                    (lowerTail : ℤ)) =
                0 :=
            TraceAnalyticMotivicTStructure
              .abelianEnvelopeTruncGEProjectionMap_f_of_decompositionLowerTail
                cut
                complex
                lowerTail
          Eq.trans
            (congrArg
              (fun upperComponent =>
                (TraceAnalyticMotivicTStructure
                  .abelianEnvelopeCochainDecompositionLowerMap
                    cut
                    complex).f
                    (TraceAnalyticMotivicTStructure.decompositionLowerCut cut -
                      (lowerTail : ℤ)) ≫
                  upperComponent)
              upperZero)
            (comp_zero
              ((TraceAnalyticMotivicTStructure
                .abelianEnvelopeCochainDecompositionLowerMap
                  cut
                  complex).f
                  (TraceAnalyticMotivicTStructure.decompositionLowerCut cut -
                    (lowerTail : ℤ))))

/-- The abelian-envelope normalized truncation decomposition has zero
composite. -/
theorem abelianEnvelopeCochainDecompositionCompositeMap_zero
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionCompositeMap cut complex =
      0 :=
  HomologicalComplex.hom_ext
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionCompositeMap cut complex)
    0
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionCompositeMap_f cut complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
