import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.Owner

/-!
# Isomorphism criterion for the exact-completion boundary comparison

The exact-completion boundary object is the presheaf cokernel of the
represented incoming differential.  If the represented analytic opcycles
boundary object also carries the same cokernel property, then the canonical
comparison between the two cokernel presentations is an isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- If the represented analytic boundary component is a cokernel of the
represented incoming differential, then the exact-completion cokernel boundary
object is canonically isomorphic to the represented analytic opcycles boundary
object. -/
def exactCompletionNormalizedConeComparisonBoundaryIsoRepresentedOfIsCokernel
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (hrepresented :
      IsColimit
        (CokernelCofork.ofπ
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
              cut
              complex
              tail
              htail
              hboundary).g
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
              cut
              complex
              tail
              htail
              hboundary).zero)) :
    TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryCokernel
          cut
          complex ≅
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
        ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
          cut) :=
  let incoming :
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.X (cut - 1)) ⟶
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.X cut) :=
    (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
      (complex.d (cut - 1) cut)
  let exactProjection :
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.X cut) ⟶
        TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            cut
            complex :=
    TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProjection
        cut
        complex
  let representedProjection :
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.X cut) ⟶
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) :=
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).g
  let comparison :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            cut
            complex ⟶
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) :=
    TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryToRepresented
        cut
        complex
        tail
        htail
        hboundary
  let exactZero :
      incoming ≫ exactProjection = 0 :=
    cokernel.condition incoming
  let exactCokernel :
      IsColimit
        (CokernelCofork.ofπ exactProjection exactZero) :=
    TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProjection_isCokernel
        cut
        complex
  let exactCofork :
      CokernelCofork incoming :=
    CokernelCofork.ofπ exactProjection exactZero
  let inverse :
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) ⟶
        TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            cut
            complex :=
    hrepresented.desc exactCofork
  let represented_inverse :
      representedProjection ≫ inverse = exactProjection :=
    hrepresented.fac exactCofork WalkingParallelPair.one
  let exact_comparison :
      exactProjection ≫ comparison = representedProjection :=
    Eq.trans
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented_fac
          cut
          complex
          tail
          htail
          hboundary)
      (Eq.symm
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g
            cut
            complex
            tail
            htail
            hboundary))
  { hom := comparison
    inv := inverse
    hom_inv_id :=
      Cofork.IsColimit.hom_ext exactCokernel
        (Eq.trans
          (Category.assoc exactProjection comparison inverse)
          (Eq.trans
            (congrArg
              (fun morphism => morphism ≫ inverse)
              exact_comparison)
            (Eq.trans
              represented_inverse
              (Eq.symm (Category.comp_id exactProjection)))))
    inv_hom_id :=
      Cofork.IsColimit.hom_ext hrepresented
        (Eq.trans
          (Category.assoc representedProjection inverse comparison)
          (Eq.trans
            (congrArg
              (fun morphism => morphism ≫ comparison)
              represented_inverse)
            (Eq.trans
              exact_comparison
              (Eq.symm (Category.comp_id representedProjection))))) }

/-- The canonical exact-completion comparison is an isomorphism whenever the
represented analytic boundary component is a cokernel of the represented
incoming differential. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_represented_isCokernel
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (hrepresented :
      IsColimit
        (CokernelCofork.ofπ
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
              cut
              complex
              tail
              htail
              hboundary).g
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
              cut
              complex
              tail
              htail
              hboundary).zero)) :
    IsIso
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          cut
          complex
          tail
          htail
          hboundary) :=
  let comparisonIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            cut
            complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) :=
    TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryIsoRepresentedOfIsCokernel
        cut
        complex
        tail
        htail
        hboundary
        hrepresented
  comparisonIso.isIso_hom

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
