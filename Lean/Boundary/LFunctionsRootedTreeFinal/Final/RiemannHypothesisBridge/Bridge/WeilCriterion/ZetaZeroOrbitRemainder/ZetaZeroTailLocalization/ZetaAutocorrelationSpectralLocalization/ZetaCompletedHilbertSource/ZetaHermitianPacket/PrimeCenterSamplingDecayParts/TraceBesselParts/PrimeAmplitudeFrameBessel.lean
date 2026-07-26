import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeAmplitudeFrameSummability

/-!
# Prime amplitude frame Bessel source

This file owns the Hilbert-frame Bessel estimate for the completed prime
spectral amplitude coordinates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- Hilbert-frame Bessel domination for the completed prime spectral amplitude
evaluation windows. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_bessel_frame_source
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.window N,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_frame_source
      f with
  | ⟨C, hC⟩ =>
      let hwindow :
          ∀ N : ℕ,
            ∑ index in ZetaPrimePowerIndex.window N,
              ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
        fun N => hC (ZetaPrimePowerIndex.window N)
      Exists.intro C hwindow

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
