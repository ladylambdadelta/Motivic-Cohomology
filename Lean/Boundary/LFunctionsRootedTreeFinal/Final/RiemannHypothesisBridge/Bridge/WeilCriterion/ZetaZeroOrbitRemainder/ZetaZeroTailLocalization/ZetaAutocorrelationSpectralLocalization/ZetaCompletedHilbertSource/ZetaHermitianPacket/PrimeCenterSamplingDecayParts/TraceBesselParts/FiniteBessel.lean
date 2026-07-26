import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingTraceEnergy

/-!
# Prime-center finite Bessel source

This file owns the finite trace-shadow Bessel estimate for the weighted
completed prime-center sampling stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- Source finite-subtrace Bessel domination for the positive weighted
completed prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_from_box_bessel_source
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C :=
  completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_traceEnergy_source
    f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
