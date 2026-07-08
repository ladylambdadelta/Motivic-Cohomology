import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryComponent.Owner

/-!
# Analytic boundary exactness for the normalized cone comparison

This file records the boundary exactness theorem that replaces the false
objectwise short-exact claim at the truncation cut.  At the boundary degree,
the original-complex summand of the normalized cone-to-upper comparison is not
an isomorphism; it is the opcycles quotient map.  The correct analytic
statement is therefore that this component is the cokernel of the incoming
differential.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- The boundary component of the normalized cone-to-upper comparison is
analytically exact: after restricting to the original-complex summand, it is
the opcycles cokernel of the incoming differential. -/
theorem additiveNormalizedConeComparison_boundary_component_isCokernel
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
    IsColimit
      (CokernelCofork.ofπ
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
              .additiveNormalizedConeComparisonCochainMap_inr_f_isCokernel_incoming
                cut
                complex
                tail
                htail
                hboundary).cocone.condition)) :=
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonCochainMap_inr_f_isCokernel_incoming
      cut
      complex
      tail
      htail
      hboundary

/-- The same boundary exactness theorem, phrased with the explicit opcycles
normal form of the boundary projection. -/
theorem additiveNormalizedConeComparison_boundary_opcycles_isCokernel
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
    IsColimit
      (CokernelCofork.ofπ
        (complex.pOpcycles cut ≫
          (complex.truncGEXIsoOpcycles
            (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
            htail
            hboundary).inv)
        (by
          exact
            (TraceAnalyticMotivicTStructure
              .additiveTruncGEProjectionBoundaryComponent_isCokernel_incoming
                cut
                complex
                tail
                htail
                hboundary).cocone.condition)) :=
  TraceAnalyticMotivicTStructure
    .additiveTruncGEProjectionBoundaryComponent_isCokernel_incoming
      cut
      complex
      tail
      htail
      hboundary

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
