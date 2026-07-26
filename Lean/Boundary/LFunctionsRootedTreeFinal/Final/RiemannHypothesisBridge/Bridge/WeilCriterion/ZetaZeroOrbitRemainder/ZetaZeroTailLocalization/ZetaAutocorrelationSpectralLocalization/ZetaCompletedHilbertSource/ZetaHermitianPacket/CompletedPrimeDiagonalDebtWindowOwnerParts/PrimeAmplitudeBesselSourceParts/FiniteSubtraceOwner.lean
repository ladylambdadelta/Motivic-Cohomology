import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingTraceEnergy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.ProjectionEnergyCore

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_traceEnergy_transport
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_traceEnergy_owner_source
      f with
  | ⟨C, hC⟩ =>
      ⟨C, fun s =>
        Eq.subst
          (motive := fun value : ℝ => value ≤ C)
          (Finset.sum_congr
            (Eq.refl s)
            (fun index membership =>
              (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
                index f).trans
                (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
                  index f))).symm
          (hC s)⟩

/-- The unconditional positive-kernel finite-subtrace Bessel bound owned by
the completed weighted prime-center sampling layer. -/
theorem completedWeightedPrimeSamplingFiniteSubtraceBound_owner
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C :=
  completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_traceEnergy_owner_source
    f

/-- The upstream positive-kernel finite-subtrace estimate transported to the
projection-energy representation used by the completed-prime owner. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_bddAbove_owner
    (f : ZetaAdmissibleFunction) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f)) :=
  match
    completedWeightedPrimeSamplingFiniteSubtraceBound_owner f with
  | ⟨C, hC⟩ =>
      ⟨C, fun value hvalue =>
        match hvalue with
        | ⟨s, hs⟩ =>
            Eq.subst
              (motive := fun projection : ℝ => projection ≤ C)
              (completedWeightedPrimeSamplingProjectionEnergy_eq_sum_hilbertFrame
                s f).symm
              (hC s)⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
