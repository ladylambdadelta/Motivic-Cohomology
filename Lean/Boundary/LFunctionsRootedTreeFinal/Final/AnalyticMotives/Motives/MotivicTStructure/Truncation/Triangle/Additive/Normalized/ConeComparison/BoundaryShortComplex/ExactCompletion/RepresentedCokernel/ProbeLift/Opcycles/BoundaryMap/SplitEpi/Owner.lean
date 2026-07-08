import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.ProbeLift.Opcycles.BoundaryMap.Owner

/-!
# Split-epi represented opcycles boundary map

This file proves epicity of the represented boundary map directly from the
categorical boundary-map normal form: a split-epic analytic opcycles projection
remains split-epic after Yoneda and after transport through the boundary
truncation isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The represented inverse boundary truncation isomorphism is split-epic. -/
theorem representedBoundaryTruncationIso_inv_isSplitEpi
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    IsSplitEpi
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        ((_root_.HomologicalComplex.truncGEXIsoOpcycles
          complex
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
          htail
          hboundary).inv)) :=
  let truncIso :=
    _root_.HomologicalComplex.truncGEXIsoOpcycles
      complex
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      htail
      hboundary
  let representedInv :
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.opcycles cut) ⟶
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) :=
    (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map truncIso.inv
  let representedHom :
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) ⟶
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.opcycles cut) :=
    (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map truncIso.hom
  IsSplitEpi.mk'
    { section_ := representedHom
      id :=
        Eq.trans
          (Eq.symm
            ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map_comp
              truncIso.hom
              truncIso.inv))
          (Eq.trans
            (congrArg
              (fun morphism =>
                (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
                  morphism)
              truncIso.hom_inv_id)
            ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map_id
              ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
                cut))) }

/-- If the analytic opcycles projection is split-epic, then the represented
boundary map is split-epic. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isSplitEpi_of_opcycles_isSplitEpi
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (opcyclesSplit : IsSplitEpi (complex.pOpcycles cut))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    IsSplitEpi
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
          cut
          complex
          tail
          htail
          hboundary).g :=
  let representedProjection :
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.X cut) ⟶
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.opcycles cut) :=
    (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
      (complex.pOpcycles cut)
  let representedInv :
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.opcycles cut) ⟶
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) :=
    (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
      ((_root_.HomologicalComplex.truncGEXIsoOpcycles
        complex
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        htail
        hboundary).inv)
  let splitProjection :
      SplitEpi representedProjection :=
    opcyclesSplit.exists_splitEpi.some.map
      TraceAnalyticAdditiveAbelianEnvelope.yoneda
  let splitInv :
      IsSplitEpi representedInv :=
    TraceAnalyticMotivicTStructure
      .representedBoundaryTruncationIso_inv_isSplitEpi
        cut
        complex
        tail
        htail
        hboundary
  let splitComposite :
      IsSplitEpi (representedProjection ≫ representedInv) :=
    IsSplitEpi.mk'
      (splitProjection.comp splitInv.exists_splitEpi.some)
  Eq.subst
    (motive := fun morphism => IsSplitEpi morphism)
    (Eq.symm
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_opcycles_factor
          cut
          complex
          tail
          htail
          hboundary))
    splitComposite

/-- If the analytic opcycles projection is split-epic, then the represented
boundary map is epic. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_epi_of_opcycles_isSplitEpi
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (opcyclesSplit : IsSplitEpi (complex.pOpcycles cut))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    Epi
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
          cut
          complex
          tail
          htail
          hboundary).g :=
  let splitBoundary :
      IsSplitEpi
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
            cut
            complex
            tail
            htail
            hboundary).g :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isSplitEpi_of_opcycles_isSplitEpi
        cut
        complex
        opcyclesSplit
        tail
        htail
        hboundary
  splitBoundary.exists_splitEpi.some.epi

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
