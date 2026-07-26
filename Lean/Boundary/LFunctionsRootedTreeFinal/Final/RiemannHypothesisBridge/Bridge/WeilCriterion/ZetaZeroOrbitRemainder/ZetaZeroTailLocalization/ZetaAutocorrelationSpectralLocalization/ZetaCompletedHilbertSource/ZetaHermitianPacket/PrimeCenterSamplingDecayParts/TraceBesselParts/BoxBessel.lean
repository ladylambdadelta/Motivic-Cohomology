import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingTraceEnergy

/-!
# Prime-center box Bessel source

This file owns rectangular-box Bessel domination for the weighted completed
prime-center sampling stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- Source rectangular-box Bessel domination for the positive weighted
completed prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_bessel_source_primitive
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.box N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_traceEnergy_source
      f with
  | ⟨C, hC⟩ =>
      let hbox :
          ∀ N : ℕ,
            ∑ index in ZetaPrimePowerIndex.box N,
              completedAutocorrelationSpectralTransform_weightedPrimeSampling
                index f ≤ C :=
        fun N => hC (ZetaPrimePowerIndex.box N)
      Exists.intro C hbox

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
