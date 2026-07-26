import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.PrimeAmplitudeHilbertFrameSource

/-!
# Positive completed prime weighted-sample summability source

This file owns the narrow summability input for the positive completed
prime weighted-sample stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed weighted prime-center sampling stream is summable at the
sampling-source level. -/
theorem completedWeightedPrimeSampling_summable_windowSource
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  completedWeightedPrimeSampling_summable_hilbertTrace_source f

/-- The positive completed prime weighted sample norm-square stream is
summable. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_summable_windowSource
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq index f) :=
  (completedWeightedPrimeSampling_summable_windowSource f).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
        index f).symm)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
