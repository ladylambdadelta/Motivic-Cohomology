import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.ExactTransport.Owner

/-!
# Numerator orthogonality for derived analytic fractions

This file owns the numerator-localization step in the represented chain-level
orthogonality proof.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Adjacent exactness bounds force the numerator of a left fraction to map
to zero after derived localization. -/
theorem exactAtBounds_leftFraction_numerator_maps_to_zero
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    (fraction :
      TraceAnalyticDerivedMotiveCategory
        .DerivedLeftFraction sourceComplex targetComplex)
    (sourceExact :
      ∀ degree : ℤ,
        0 < degree →
          sourceComplex.ExactAt degree)
    (auxiliaryExact :
      ∀ degree : ℤ,
        degree < 1 →
          fraction.Y'.ExactAt degree) :
    TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        fraction.f =
      0 :=
  TraceAnalyticDerivedMotiveCategory
    .exactAtBounds_leftFraction_numerator_maps_to_zero_from_strict_transport
      sourceComplex
      targetComplex
      fraction
      sourceExact
      auxiliaryExact

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
