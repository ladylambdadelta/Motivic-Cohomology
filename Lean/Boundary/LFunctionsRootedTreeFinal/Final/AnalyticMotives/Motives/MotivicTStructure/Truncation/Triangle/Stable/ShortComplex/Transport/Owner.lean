import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.ShortComplex.Owner

/-!
# Verdier transport of the lower-inclusion truncation short complex

This file applies the Verdier quotient functor directly to the additive
lower-inclusion short complex and exposes the transported object and morphism
projections.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The Verdier-transported additive lower-inclusion short complex. -/
def stableTransportedLowerInclusionShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    ShortComplex TraceAnalyticStableMotiveCategory :=
  (TraceAnalyticMotivicTStructure.additiveLowerInclusionShortComplex
    cut
    complex).map TraceAnalyticStableMotiveCategory.quotientFunctor

/-- The first object of the transported short complex is the stable lower
truncation. -/
theorem stableTransportedLowerInclusionShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableTransportedLowerInclusionShortComplex
      cut
      complex).X₁ =
      TraceAnalyticMotivicTStructure.stableTruncLE cut complex :=
  rfl

/-- The second object of the transported short complex is the stable image of
the original complex. -/
theorem stableTransportedLowerInclusionShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableTransportedLowerInclusionShortComplex
      cut
      complex).X₂ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) :=
  rfl

/-- The third object of the transported short complex is the Verdier image of
the additive lower-inclusion cone vertex. -/
theorem stableTransportedLowerInclusionShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableTransportedLowerInclusionShortComplex
      cut
      complex).X₃ =
      TraceAnalyticStableMotiveCategory.objectOf
        (TraceAnalyticMotivicTStructure.additiveLowerInclusionConeVertex
          cut
          complex) :=
  rfl

/-- The first map of the transported short complex is the stable lower
truncation inclusion. -/
theorem stableTransportedLowerInclusionShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableTransportedLowerInclusionShortComplex
      cut
      complex).f =
      TraceAnalyticMotivicTStructure.stableTruncLEInclusionMap
        cut
        complex :=
  congrArg
    (fun morphism =>
      TraceAnalyticStableMotiveCategory.quotientFunctor.map morphism)
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionShortComplex_f
      cut
      complex)

/-- The second map of the transported short complex is the Verdier image of the
additive cone map. -/
theorem stableTransportedLowerInclusionShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableTransportedLowerInclusionShortComplex
      cut
      complex).g =
      TraceAnalyticStableMotiveCategory.mapOf
        (TraceAnalyticMotivicTStructure.additiveLowerInclusionConeMap
          cut
          complex) :=
  rfl

/-- The transported lower-inclusion map followed by the transported cone map is
zero after Verdier localization. -/
theorem stableTransportedLowerInclusionShortComplex_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableTransportedLowerInclusionShortComplex
      cut
      complex).f ≫
        (TraceAnalyticMotivicTStructure.stableTransportedLowerInclusionShortComplex
          cut
          complex).g =
      0 :=
  (TraceAnalyticMotivicTStructure.stableTransportedLowerInclusionShortComplex
    cut
    complex).zero

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
