import Mathlib.Algebra.Homology.ShortComplex.Exact
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.AnalyticBoundaryExact.Owner

/-!
# Boundary short complex for the normalized cone comparison

This file converts the analytic boundary cokernel theorem into exactness of
the corresponding boundary short complex.  The short complex is deliberately
not the false objectwise truncation complex `LE ⟶ K ⟶ GE`; its second map is
the actual original-complex summand of the normalized cone-to-upper comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The additive boundary short complex whose second map is the actual
original-complex summand of the normalized cone-to-upper comparison at the
cut. -/
def additiveNormalizedConeComparisonBoundaryShortComplex
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
    ShortComplex TraceAnalyticAdditiveCategoryObject :=
  ShortComplex.mk
    (complex.d (cut - 1) cut)
    (((CochainComplex.mappingCone.inr
        (TraceAnalyticMotivicTStructure
          .additiveNormalizedCochainDecompositionLowerMap
            cut
            complex)).f cut) ≫
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonCochainMap
          cut
          complex).f cut)
    (by
      exact
        (TraceAnalyticMotivicTStructure
          .additiveNormalizedConeComparison_boundary_component_isCokernel
            cut
            complex
            tail
            htail
            hboundary).cocone.condition)

/-- The second map of the boundary short complex is the normalized
cone-to-upper comparison restricted to the original-complex summand. -/
theorem additiveNormalizedConeComparisonBoundaryShortComplex_g
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
      .additiveNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).g =
      (((CochainComplex.mappingCone.inr
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedCochainDecompositionLowerMap
              cut
              complex)).f cut) ≫
        (TraceAnalyticMotivicTStructure
          .additiveNormalizedConeComparisonCochainMap
            cut
            complex).f cut) :=
  rfl

/-- The boundary short complex is exact once its homology object exists: the
analytic boundary component theorem proves that its second map is a cokernel
of the incoming differential. -/
theorem additiveNormalizedConeComparisonBoundaryShortComplex_exact
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
    [ShortComplex.HasHomology
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBoundaryShortComplex
          cut
          complex
          tail
          htail
          hboundary)] :
    (TraceAnalyticMotivicTStructure
      .additiveNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).Exact :=
  ShortComplex.exact_of_g_is_cokernel
    (TraceAnalyticMotivicTStructure
      .additiveNormalizedConeComparison_boundary_component_isCokernel
        cut
        complex
        tail
        htail
        hboundary)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
