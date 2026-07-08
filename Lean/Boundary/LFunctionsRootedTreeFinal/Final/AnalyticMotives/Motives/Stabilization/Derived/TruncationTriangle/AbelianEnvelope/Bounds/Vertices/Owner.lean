import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.AbelianEnvelope.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Bounds.Owner

/-!
# Bounds for intrinsic abelian-envelope derived truncation vertices

This file attaches the homological bounds of the intrinsic abelian-envelope
truncation complexes to the first and third vertices of the corresponding
derived distinguished triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The first object of the intrinsic abelian-envelope derived truncation
triangle lies in the lower homological bound determined by the normalized lower
cut. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle_obj₁_homologicalLE
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    TraceAnalyticDerivedMotiveCategory.HomologicalLE
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
          cut
          complex
          hshortExact).obj₁ :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeTruncLE_derived_homologicalLE
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
      complex

/-- The third object of the intrinsic abelian-envelope derived truncation
triangle lies in the upper homological bound determined by the cut. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle_obj₃_homologicalGE
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    TraceAnalyticDerivedMotiveCategory.HomologicalGE
      cut
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionDerivedTriangle
          cut
          complex
          hshortExact).obj₃ :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeTruncGE_derived_homologicalGE
      cut
      complex

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
