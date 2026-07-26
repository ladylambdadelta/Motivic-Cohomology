import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingTraceEnergy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingDiagonalDebtMajorant

/-!
# Conditional prime weighted sampling trace-energy consequences

This file owns the trace-energy consequences that are available once the
completed diagonal-debt real-coordinate `HasSum` inputs have been supplied.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A reflected diagonal-debt real-coordinate `HasSum` gives summability of
the opposite completed prime spectral-amplitude square stream. -/
theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        C) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_diagonalDebtCoordinate_re_hasSum_traceEnergy_free_source
    f C hhasSum

/-- Diagonal-debt real-coordinate `HasSum` inputs for a probe and its
reflected probe give summability of the completed prime spectral-coordinate
majorant. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_free_source
    f C Creflect hhasSum hhasSumReflect

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
