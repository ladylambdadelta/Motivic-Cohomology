import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.CompositeZero.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.Target.Owner

/-!
# Normalized additive cone-to-upper map

This file constructs the cochain-level map from the mapping cone of the
normalized lower inclusion to the upper truncation.  The map is obtained from
the mapping-cone descent constructor: it is zero on the shifted lower summand
and is the upper truncation projection on the original-complex summand.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open HomologicalComplex
open HomologicalComplex.HomComplex

namespace TraceAnalyticMotivicTStructure

/-- The descent equation for the normalized cone-to-upper cochain map: the
lower inclusion followed by the upper projection is zero. -/
theorem additiveNormalizedConeComparisonCochainMap_desc_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    δ (-1) 0
        (0 :
          Cochain
            (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
              cut
              complex)
            (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)
            (-1)) =
      Cochain.ofHom
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
            cut
            complex ≫
          TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
            cut
            complex) :=
  let composite_eq :
      TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
          cut
          complex ≫
        TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
          cut
          complex =
        0 :=
    Eq.trans
      (Eq.symm
        (TraceAnalyticMotivicTStructure.additiveCochainDecompositionCompositeMap_eq
          cut
          complex))
      (TraceAnalyticMotivicTStructure.additiveCochainDecompositionCompositeMap_zero
        cut
        complex)
  let ofHom_composite_eq_zero :
      Cochain.ofHom
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
            cut
            complex ≫
          TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
            cut
            complex) =
        0 :=
    Eq.trans
      (congrArg Cochain.ofHom composite_eq)
      (Cochain.ofHom_zero
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
          cut
          complex)
        (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex))
  Eq.trans
    (δ_zero :
      δ (-1) 0
          (0 :
            Cochain
              (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
                cut
                complex)
              (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)
              (-1)) =
        0)
    (Eq.symm ofHom_composite_eq_zero)

/-- The cochain-level cone-to-upper map for the normalized lower-inclusion
mapping cone. -/
def additiveNormalizedConeComparisonCochainMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
          cut
          complex) ⟶
      TraceAnalyticMotivicTStructure.additiveTruncGE cut complex :=
  CochainComplex.mappingCone.desc
    (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
      cut
      complex)
    (0 :
      Cochain
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
          cut
          complex)
        (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)
        (-1))
    (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
      cut
      complex)
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap_desc_eq
      cut
      complex)

/-- The cone-to-upper cochain map is zero on the shifted lower summand. -/
theorem additiveNormalizedConeComparisonCochainMap_inl
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (CochainComplex.mappingCone.inl
      (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
        cut
        complex)).comp
        (Cochain.ofHom
          (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
            cut
            complex))
        (add_zero (-1)) =
      (0 :
        Cochain
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
            cut
            complex)
          (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)
          (-1)) :=
  CochainComplex.mappingCone.inl_desc
    (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
      cut
      complex)
    (0 :
      Cochain
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
          cut
          complex)
        (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)
        (-1))
    (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
      cut
      complex)
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap_desc_eq
      cut
      complex)

/-- The cone-to-upper cochain map restricts along the original-complex summand
to the upper truncation projection. -/
theorem additiveNormalizedConeComparisonCochainMap_inr
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    CochainComplex.mappingCone.inr
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
          cut
          complex) ≫
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex =
      TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
        cut
        complex :=
  CochainComplex.mappingCone.inr_desc
    (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
      cut
      complex)
    (0 :
      Cochain
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
          cut
          complex)
        (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)
        (-1))
    (TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
      cut
      complex)
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap_desc_eq
      cut
      complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
