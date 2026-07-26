import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingTraceEnergy

/-!
# Prime-center genuine-window Bessel source

This file owns genuine-window Bessel domination for the weighted completed
prime-center sampling stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- Source genuine-window Bessel domination for the positive weighted
completed prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_window_bessel_source_primitive
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.window N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_traceEnergy_source
      f with
  | ⟨C, hC⟩ =>
      let hwindow :
          ∀ N : ℕ,
            ∑ index in ZetaPrimePowerIndex.window N,
              completedAutocorrelationSpectralTransform_weightedPrimeSampling
                index f ≤ C :=
        fun N => hC (ZetaPrimePowerIndex.window N)
      Exists.intro C hwindow

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
