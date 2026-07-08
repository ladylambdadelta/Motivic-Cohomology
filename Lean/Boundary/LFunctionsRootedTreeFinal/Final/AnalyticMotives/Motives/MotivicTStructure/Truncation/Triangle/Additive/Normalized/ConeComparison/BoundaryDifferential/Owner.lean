import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryComponent.Owner

/-!
# Boundary differential of the normalized cone comparison

This file records the mapping-cone differential formula at the boundary
source.  It is the structural input for the opcycles/cokernel exactness proof:
the boundary kernel of `pOpcycles` is supplied by the shifted lower summand of
the cone differential, not by an objectwise splitting.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The shifted-lower summand of the normalized mapping cone contributes the
lower-inclusion component to the boundary differential, up to the standard
mapping-cone lower-differential correction. -/
theorem additiveNormalizedConeComparison_boundary_inl_d
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (source target previous : ℤ)
    (hsourceTarget : source + (-1) = target)
    (hpreviousSource : previous + (-1) = source) :
    (CochainComplex.mappingCone.inl
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
          cut
          complex)).v source target hsourceTarget ≫
        (CochainComplex.mappingCone
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
            cut
            complex)).d target source =
      (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
          cut
          complex).f source ≫
        (CochainComplex.mappingCone.inr
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
            cut
            complex)).f source -
      (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
          cut
          complex).d source previous ≫
        (CochainComplex.mappingCone.inl
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
            cut
            complex)).v previous source hpreviousSource :=
  CochainComplex.mappingCone.inl_v_d
    (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
      cut
      complex)
    source
    target
    previous
    hsourceTarget
    hpreviousSource

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
