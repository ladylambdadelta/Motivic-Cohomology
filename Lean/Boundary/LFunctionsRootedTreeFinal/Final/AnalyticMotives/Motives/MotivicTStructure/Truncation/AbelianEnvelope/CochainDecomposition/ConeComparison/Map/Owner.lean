import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.CompositeZero.Owner

/-!
# Abelian-envelope cone-to-upper comparison map

This file constructs the abelian-envelope analogue of the normalized
cone-to-upper comparison map.  It is the mapping-cone descent map for the
lower inclusion in the normalized truncation decomposition: zero on the shifted
lower summand and the upper projection on the original-complex summand.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open HomologicalComplex
open HomologicalComplex.HomComplex

namespace TraceAnalyticMotivicTStructure

/-- The descent equation for the abelian-envelope normalized cone-to-upper map:
the lower inclusion followed by the upper projection is zero. -/
theorem abelianEnvelopeNormalizedConeComparisonCochainMap_desc_eq
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    δ (-1) 0
        (0 :
          Cochain
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeDecompositionTruncLE cut complex)
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeTruncGE cut complex)
            (-1)) =
      Cochain.ofHom
        (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionLowerMap cut complex ≫
          TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionUpperMap cut complex) :=
  let composite_eq :
      TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionLowerMap cut complex ≫
        TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionUpperMap cut complex =
        0 :=
    Eq.trans
      (Eq.symm
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionCompositeMap_eq cut complex))
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionCompositeMap_zero cut complex)
  let ofHom_composite_eq_zero :
      Cochain.ofHom
        (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionLowerMap cut complex ≫
          TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionUpperMap cut complex) =
        0 :=
    Eq.trans
      (congrArg Cochain.ofHom composite_eq)
      (Cochain.ofHom_zero
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeDecompositionTruncLE cut complex)
        (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex))
  Eq.trans
    (δ_zero :
      δ (-1) 0
          (0 :
            Cochain
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeDecompositionTruncLE cut complex)
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeTruncGE cut complex)
              (-1)) =
        0)
    (Eq.symm ofHom_composite_eq_zero)

/-- The abelian-envelope cochain-level cone-to-upper map for the normalized
lower-inclusion mapping cone. -/
def abelianEnvelopeNormalizedConeComparisonCochainMap
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionLowerMap cut complex) ⟶
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex :=
  CochainComplex.mappingCone.desc
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionLowerMap cut complex)
    (0 :
      Cochain
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeDecompositionTruncLE cut complex)
        (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex)
        (-1))
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionUpperMap cut complex)
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonCochainMap_desc_eq cut complex)

/-- The abelian-envelope cone-to-upper map is zero on the shifted lower
summand. -/
theorem abelianEnvelopeNormalizedConeComparisonCochainMap_inl
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    (CochainComplex.mappingCone.inl
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionLowerMap cut complex)).comp
        (Cochain.ofHom
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeNormalizedConeComparisonCochainMap cut complex))
        (add_zero (-1)) =
      (0 :
        Cochain
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeDecompositionTruncLE cut complex)
          (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex)
          (-1)) :=
  CochainComplex.mappingCone.inl_desc
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionLowerMap cut complex)
    (0 :
      Cochain
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeDecompositionTruncLE cut complex)
        (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex)
        (-1))
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionUpperMap cut complex)
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonCochainMap_desc_eq cut complex)

/-- The abelian-envelope cone-to-upper map restricts along the original-complex
summand to the upper truncation projection. -/
theorem abelianEnvelopeNormalizedConeComparisonCochainMap_inr
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    CochainComplex.mappingCone.inr
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionLowerMap cut complex) ≫
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonCochainMap cut complex =
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionUpperMap cut complex :=
  CochainComplex.mappingCone.inr_desc
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionLowerMap cut complex)
    (0 :
      Cochain
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeDecompositionTruncLE cut complex)
        (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex)
        (-1))
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionUpperMap cut complex)
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonCochainMap_desc_eq cut complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
