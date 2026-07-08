import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.YonedaExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Owner

/-!
# Yoneda exactness for the normalized stable truncation short complex

The normalized lower-inclusion truncation short complex is extracted from an
actual distinguished triangle in the stable analytic motive category.  This
file records the two homological exactness consequences used by the
truncation-as-cone layer.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Covariant preadditive Yoneda sends the normalized stable lower-inclusion
truncation short complex to an exact short complex. -/
theorem stableNormalizedLowerInclusionShortComplex_coyoneda_exact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplex cut complex).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory.coyonedaShortComplex_exact
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex)
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionTriangle_distinguished cut complex)
    probe

/-- Contravariant preadditive Yoneda sends the normalized stable
lower-inclusion truncation short complex to an exact short complex after
passing to the opposite short complex. -/
theorem stableNormalizedLowerInclusionShortComplex_yoneda_exact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : StableInfinityOwner.PresentedCategory) :
    ((TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplex cut complex).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory.yonedaShortComplex_exact
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex)
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionTriangle_distinguished cut complex)
    probe

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
