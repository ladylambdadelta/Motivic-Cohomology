import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.Map.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Map.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Boundary.Cokernel.Owner

/-!
# Boundary component of the normalized cone-to-upper map

This file identifies the original-complex summand of the normalized
cone-to-upper map at the opcycles boundary.  This is the concrete component
calculation needed before the boundary degree can be treated by cokernel
exactness rather than by a false splitting argument.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- On the original-complex summand of the mapping cone, the normalized
cone-to-upper map has boundary component `pOpcycles` followed by the inverse
extended opcycles truncation isomorphism. -/
theorem additiveNormalizedConeComparisonCochainMap_inr_f_of_boundary
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (degree : ℤ)
    (hdegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        degree)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (CochainComplex.mappingCone.inr
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
            cut
            complex)).f degree ≫
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex).f degree =
      complex.pOpcycles degree ≫
        (_root_.HomologicalComplex.truncGEXIsoOpcycles
          complex
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
          hdegree
          hboundary).inv :=
  let lowerMap :
      TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE cut complex ⟶
        complex :=
    TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
      cut
      complex
  let coneMap :
      CochainComplex.mappingCone lowerMap ⟶
        TraceAnalyticMotivicTStructure.additiveTruncGE cut complex :=
    TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
      cut
      complex
  let inrConeMap :
      CochainComplex.mappingCone.inr lowerMap ≫ coneMap =
        TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
          cut
          complex :=
    TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap_inr
      cut
      complex
  let componentEq :
      (CochainComplex.mappingCone.inr lowerMap ≫ coneMap).f degree =
        (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
          cut
          complex).f degree :=
    congrArg
      (fun hom => hom.f degree)
      inrConeMap
  let splitComponent :
      (CochainComplex.mappingCone.inr lowerMap ≫ coneMap).f degree =
        (CochainComplex.mappingCone.inr lowerMap).f degree ≫
          coneMap.f degree :=
    _root_.HomologicalComplex.comp_f
      (CochainComplex.mappingCone.inr lowerMap)
      coneMap
      degree
  Eq.trans
    (Eq.symm splitComponent)
    (Eq.trans
      componentEq
      (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap_f_of_boundary
        cut
        complex
        tail
        degree
        hdegree
        hboundary))

/-- The original-complex summand component of the normalized cone-to-upper map
at the boundary cut is a cokernel of the incoming differential. -/
theorem additiveNormalizedConeComparisonCochainMap_inr_f_isCokernel_incoming
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (hdegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    IsColimit
      (CokernelCofork.ofπ
        ((CochainComplex.mappingCone.inr
            (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
              cut
              complex)).f cut ≫
          (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
            cut
            complex).f cut)
        (let transportedProjection :
            complex.X cut ⟶
              (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X cut :=
            complex.pOpcycles cut ≫
              (_root_.HomologicalComplex.truncGEXIsoOpcycles
                complex
                (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
                hdegree
                hboundary).inv
          let componentFormula :
              (CochainComplex.mappingCone.inr
                    (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
                      cut
                      complex)).f cut ≫
                  (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
                    cut
                    complex).f cut =
                transportedProjection :=
            TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap_inr_f_of_boundary
                cut
                complex
                tail
                cut
                hdegree
                hboundary
          let transportedZero :
              complex.d (cut - 1) cut ≫ transportedProjection =
                0 :=
            Eq.trans
              (Category.assoc
                (complex.d (cut - 1) cut)
                (complex.pOpcycles cut)
                ((_root_.HomologicalComplex.truncGEXIsoOpcycles
                  complex
                  (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
                  hdegree
                  hboundary).inv))
              (Eq.trans
                (congrArg
                  (fun morphism =>
                    morphism ≫
                      (_root_.HomologicalComplex.truncGEXIsoOpcycles
                        complex
                        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
                        hdegree
                        hboundary).inv)
                  (complex.d_pOpcycles (cut - 1) cut))
                (zero_comp
                  ((_root_.HomologicalComplex.truncGEXIsoOpcycles
                    complex
                    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
                    hdegree
                    hboundary).inv)))
          Eq.trans
            (congrArg
              (fun morphism =>
                complex.d (cut - 1) cut ≫ morphism)
              componentFormula)
            transportedZero)) :=
  let transportedProjection :
      complex.X cut ⟶
        (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X cut :=
    complex.pOpcycles cut ≫
      (_root_.HomologicalComplex.truncGEXIsoOpcycles
        complex
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        hdegree
        hboundary).inv
  let componentFormula :
      (CochainComplex.mappingCone.inr
            (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
              cut
              complex)).f cut ≫
          (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
            cut
            complex).f cut =
        transportedProjection :=
    TraceAnalyticMotivicTStructure
      .additiveNormalizedConeComparisonCochainMap_inr_f_of_boundary
        cut
        complex
        tail
        cut
        hdegree
        hboundary
  let transportedIsCokernel :
      IsColimit
        (CokernelCofork.ofπ
          transportedProjection
          (Eq.trans
            (Category.assoc
              (complex.d (cut - 1) cut)
              (complex.pOpcycles cut)
              ((_root_.HomologicalComplex.truncGEXIsoOpcycles
                complex
                (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
                hdegree
                hboundary).inv))
            (Eq.trans
              (congrArg
                (fun morphism =>
                  morphism ≫
                    (_root_.HomologicalComplex.truncGEXIsoOpcycles
                      complex
                      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
                      hdegree
                      hboundary).inv)
                (complex.d_pOpcycles (cut - 1) cut))
              (zero_comp
                ((_root_.HomologicalComplex.truncGEXIsoOpcycles
                  complex
                  (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
                  hdegree
                  hboundary).inv)))) :=
    TraceAnalyticMotivicTStructure
      .additiveTruncGEProjectionBoundaryComponent_isCokernel_incoming
        cut
        complex
        tail
        hdegree
        hboundary
  IsColimit.ofIsoColimit
    transportedIsCokernel
    (Cofork.ext
      (Iso.refl _)
      (Eq.trans
        (Category.comp_id transportedProjection)
        (Eq.symm componentFormula)))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
