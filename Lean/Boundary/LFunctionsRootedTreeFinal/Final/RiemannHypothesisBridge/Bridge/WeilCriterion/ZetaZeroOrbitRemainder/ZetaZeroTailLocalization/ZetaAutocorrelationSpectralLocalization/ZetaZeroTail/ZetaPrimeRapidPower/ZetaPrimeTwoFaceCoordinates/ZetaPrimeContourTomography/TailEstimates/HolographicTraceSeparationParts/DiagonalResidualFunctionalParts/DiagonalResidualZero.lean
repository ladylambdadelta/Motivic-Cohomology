import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparation

/-!
# Diagonal residual zero source

This file owns vanishing of the real completed diagonal-debt coordinate
residual.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Source vanishing of the real completed diagonal-debt coordinate residual. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_source_primitive
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    ((Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
      ℂ) = 0 :=
  let hreal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0 :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_ownerHolographicTraceSeparation
      f hcoordinateZero
  congrArg (fun value : ℝ => (value : ℂ)) hreal

/-- Source vanishing of the real completed diagonal-debt coordinate residual,
with the positive/off-diagonal gap vanishing explicitly supplied. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_positiveOffDiagonalGap_eq_zero_source_primitive
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    ((Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
      ℂ) = 0 :=
  let hreal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0 :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_positiveOffDiagonalGap_eq_zero_ownerHolographicTraceSeparation
      f D hmajorant hgapZero
  congrArg (fun value : ℝ => (value : ℂ)) hreal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
