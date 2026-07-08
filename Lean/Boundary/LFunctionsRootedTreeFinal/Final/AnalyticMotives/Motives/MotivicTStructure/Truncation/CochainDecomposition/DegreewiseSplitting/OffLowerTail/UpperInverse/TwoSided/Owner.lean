import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.OffLowerTail.UpperInverse.ShortComplexMap.Owner

/-!
# Two-sided inverse for the off-lower-tail upper map

This file constructs the local inverse of the evaluated upper map from the
concrete nonboundary upper-truncation isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- At a nonboundary upper-tail degree, the inverse of the evaluated upper map
is the hom side of Mathlib's nonboundary upper-truncation isomorphism. -/
def additiveCochainDecompositionOffLowerTailUpperInverse
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (degree : ℤ)
    (hdegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        degree)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
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
        degree)).X₂ :=
  (_root_.HomologicalComplex.truncGEXIso
    complex
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    hdegree
    hboundary).hom

/-- The local off-lower-tail inverse followed by the evaluated upper map is the
identity on the upper truncation component. -/
theorem additiveCochainDecompositionOffLowerTailUpperInverse_s_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (degree : ℤ)
    (hdegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        degree)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    TraceAnalyticMotivicTStructure
        .additiveCochainDecompositionOffLowerTailUpperInverse
          cut
          complex
          tail
          degree
          hdegree
          hboundary ≫
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).g =
      𝟙 _ :=
  let upperIso :
      (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X degree ≅
        complex.X degree :=
    _root_.HomologicalComplex.truncGEXIso
      complex
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      hdegree
      hboundary
  let gFormula :
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).g =
        upperIso.inv :=
    TraceAnalyticMotivicTStructure
      .additiveCochainDecompositionDegreewiseUpperMap_of_not_boundary
        cut
        complex
        tail
        degree
        hdegree
        hboundary
  Eq.trans
    (congrArg
      (fun morphism =>
        TraceAnalyticMotivicTStructure
            .additiveCochainDecompositionOffLowerTailUpperInverse
              cut
              complex
              tail
              degree
              hdegree
              hboundary ≫
          morphism)
      gFormula)
    upperIso.hom_inv_id

/-- The evaluated upper map followed by the local off-lower-tail inverse is the
identity on the middle component. -/
theorem additiveCochainDecompositionOffLowerTailUpperInverse_g_s
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (degree : ℤ)
    (hdegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        degree)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveCategoryObject
        (ComplexShape.up ℤ)
        degree)).g ≫
      TraceAnalyticMotivicTStructure
        .additiveCochainDecompositionOffLowerTailUpperInverse
          cut
          complex
          tail
          degree
          hdegree
          hboundary =
      𝟙 _ :=
  let upperIso :
      (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X degree ≅
        complex.X degree :=
    _root_.HomologicalComplex.truncGEXIso
      complex
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      hdegree
      hboundary
  let gFormula :
      ((TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveCategoryObject
          (ComplexShape.up ℤ)
          degree)).g =
        upperIso.inv :=
    TraceAnalyticMotivicTStructure
      .additiveCochainDecompositionDegreewiseUpperMap_of_not_boundary
        cut
        complex
        tail
        degree
        hdegree
        hboundary
  Eq.trans
    (congrArg
      (fun morphism =>
        morphism ≫
          TraceAnalyticMotivicTStructure
            .additiveCochainDecompositionOffLowerTailUpperInverse
              cut
              complex
              tail
              degree
              hdegree
              hboundary)
      gFormula)
    upperIso.inv_hom_id

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
