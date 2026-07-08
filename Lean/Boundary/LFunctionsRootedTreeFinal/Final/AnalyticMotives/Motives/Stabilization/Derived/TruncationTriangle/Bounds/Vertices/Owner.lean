import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Bounds.Owner

/-!
# Bounds for the actual derived truncation-triangle vertices

This file attaches the homological bounds proved for represented truncation
complexes to the first and third objects of the distinguished derived
truncation triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The first object of the derived truncation triangle lies in the lower
homological bound determined by the normalized lower cut. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangle_obj₁_homologicalLE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangle
          cut
          complex
          hshortExact).obj₁ :=
  TraceAnalyticMotivicTStructure
    .yonedaCochainComplex_additiveDecompositionTruncLE_derived_homologicalLE
      cut
      complex

/-- The third object of the derived truncation triangle lies in the upper
homological bound determined by the cut. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangle_obj₃_homologicalGE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE
      cut
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangle
          cut
          complex
          hshortExact).obj₃ :=
  TraceAnalyticMotivicTStructure
    .yonedaCochainComplex_additiveTruncGE_derived_homologicalGE
      cut
      complex

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
