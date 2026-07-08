import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.AbelianEnvelope.Bounds.Vertices.Owner

/-!
# Truncation existence from intrinsic abelian-envelope short exactness

This file turns a concrete short-exact witness for the intrinsic
abelian-envelope truncation sequence into the derived analytic truncation
existence statement.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- Intrinsic abelian-envelope short exactness gives the object-level
truncation triangle for the localized input complex. -/
theorem abelianEnvelopeIntrinsic_exists_truncation_triangle
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper ∧
          ∃ (firstMap :
              lower ⟶
                TraceAnalyticDerivedMotiveCategory.objectOf complex)
            (secondMap :
              TraceAnalyticDerivedMotiveCategory.objectOf complex ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  Exists.intro
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).obj₁
    (Exists.intro
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
          cut
          complex
          hshortExact).obj₃
      (And.intro
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle_obj₁_homologicalLE
            cut
            complex
            hshortExact)
        (And.intro
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle_obj₃_homologicalGE
              cut
              complex
              hshortExact)
          (Exists.intro
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
                cut
                complex
                hshortExact).mor₁
            (Exists.intro
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
                  cut
                  complex
                  hshortExact).mor₂
              (Exists.intro
                (TraceAnalyticMotivicTStructure
                  .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
                    cut
                    complex
                    hshortExact).mor₃
                (TraceAnalyticMotivicTStructure
                  .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle_distinguished
                    cut
                    complex
                    hshortExact))))))

/-- Normalized intrinsic abelian-envelope short exactness gives the adjacent
`≤ 0` and `≥ 1` truncation triangle for the localized input complex. -/
theorem abelianEnvelopeIntrinsic_exists_triangle_zero_one
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            complex)) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper ∧
          ∃ (firstMap :
              lower ⟶
                TraceAnalyticDerivedMotiveCategory.objectOf complex)
            (secondMap :
              TraceAnalyticDerivedMotiveCategory.objectOf complex ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsic_exists_truncation_triangle
      1
      complex
      hshortExact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
