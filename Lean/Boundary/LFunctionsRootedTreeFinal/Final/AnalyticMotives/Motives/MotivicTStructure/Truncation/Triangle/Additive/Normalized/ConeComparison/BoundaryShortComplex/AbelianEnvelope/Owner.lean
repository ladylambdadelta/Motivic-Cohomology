import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.YonedaComplex.Homology.Owner

/-!
# Abelian-envelope boundary short complex for the normalized cone comparison

This file moves the analytic boundary short complex for the normalized
cone-to-upper comparison into the represented abelian envelope and then into
its concrete probe-degree Q-module evaluations.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The represented abelian-envelope image of the analytic boundary short
complex for the normalized cone comparison. -/
def abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
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
    ShortComplex TraceAnalyticAdditiveAbelianEnvelope :=
  (TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonBoundaryShortComplex
      cut
      complex
      tail
      htail
      hboundary).map
        TraceAnalyticAdditiveAbelianEnvelope.yoneda

/-- The first represented object in the boundary short complex is the object
in degree `cut - 1` of the original analytic cochain complex. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_X₁
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
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).X₁ =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
        (complex.X (cut - 1)) :=
  rfl

/-- The middle represented object in the boundary short complex is the object
in degree `cut` of the original analytic cochain complex. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_X₂
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
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).X₂ =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
        (complex.X cut) :=
  rfl

/-- The third represented object in the boundary short complex is the boundary
degree object of the upper truncation. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_X₃
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
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).X₃ =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
        ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
          cut) :=
  rfl

/-- The first represented map in the boundary short complex is the Yoneda
image of the incoming analytic differential. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_f
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
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).f =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        (complex.d (cut - 1) cut) :=
  rfl

/-- The second represented map in the boundary short complex is the Yoneda
image of the original-complex summand of the normalized cone comparison. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g
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
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).g =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        ((((CochainComplex.mappingCone.inr
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedCochainDecompositionLowerMap
                cut
                complex)).f cut) ≫
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap
              cut
              complex).f cut)) :=
  rfl

/-- The represented boundary short complex has homology because the analytic
abelian envelope is an abelian presheaf category. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_hasHomology
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
    ShortComplex.HasHomology
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
          cut
          complex
          tail
          htail
          hboundary) :=
  CategoryWithHomology.hasHomology
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary)

/-- Probe evaluation of the represented boundary short complex. -/
def abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
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
    (probe : TraceAnalyticAdditiveCategoryObject) :
    ShortComplex (ModuleCat Rat) :=
  (TraceAnalyticMotivicTStructure
    .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
      cut
      complex
      tail
      htail
      hboundary).map
        (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)

/-- The first map of the evaluated boundary short complex is precomposition
with the incoming analytic differential. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_f
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
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        tail
        htail
        hboundary
        probe).f =
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        (complex.d (cut - 1) cut)).app
        (Opposite.op probe) :=
  rfl

/-- The second map of the evaluated boundary short complex is the probe
evaluation of the normalized cone boundary component. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_g
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
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        tail
        htail
        hboundary
        probe).g =
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        ((((CochainComplex.mappingCone.inr
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedCochainDecompositionLowerMap
                cut
                complex)).f cut) ≫
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap
              cut
              complex).f cut))).app
        (Opposite.op probe) :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
