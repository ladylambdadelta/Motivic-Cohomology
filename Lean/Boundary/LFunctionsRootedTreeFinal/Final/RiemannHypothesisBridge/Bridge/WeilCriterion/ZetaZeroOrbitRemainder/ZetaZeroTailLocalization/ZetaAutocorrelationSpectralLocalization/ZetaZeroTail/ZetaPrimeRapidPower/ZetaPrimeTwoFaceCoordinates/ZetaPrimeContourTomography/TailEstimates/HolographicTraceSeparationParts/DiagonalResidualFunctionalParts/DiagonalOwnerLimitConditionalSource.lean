import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalOwnerLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.PositiveRealWindowLimitConditionalSource

/-!
# Conditional diagonal owner-limit source

This file isolates the explicit `HasSum` compatibility layer for diagonal
owner-window convergence. The active owner file keeps only coordinate-zero and
gap-zero inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give convergence of
real diagonal-debt windows to the owner completed diagonal-debt real part. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_primitive
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
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
  let htwoFace :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))) :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_ownerMatrixCoefficient_re_of_diagonalDebtCoordinate_re_hasSum_source_primitive
      f C Creflect hhasSum hhasSumReflect
  let hpositive :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_ownerPositiveChannel_of_diagonalDebtCoordinate_re_hasSum_source_primitive
      f C Creflect hhasSum hhasSumReflect
  let hadd :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝
          (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) +
            completedPrimeDefectKernelPositiveChannel f)) :=
    htwoFace.add hpositive
  let htargetOrder :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) +
          completedPrimeDefectKernelPositiveChannel f =
        completedPrimeDefectKernelPositiveChannel f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    add_comm
      (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
      (completedPrimeDefectKernelPositiveChannel f)
  let howner :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) +
          completedPrimeDefectKernelPositiveChannel f =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    htargetOrder.trans
      (zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_positiveChannel_add_twoFace_re_source_primitive
        f).symm
  let haddOwner :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
    Eq.subst
      (motive := fun value : ℝ =>
        Tendsto
          (fun N : ℕ =>
            Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
              zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
          atTop
          (𝓝 value))
      howner
      hadd
  Eq.subst
    (motive := fun stream : ℕ → ℝ =>
      Tendsto stream atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))))
    (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_stream_eq_twoFace_re_add_positiveRealWindow_source
      f).symm
    haddOwner

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
