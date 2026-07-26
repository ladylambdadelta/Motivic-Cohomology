import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.CompletedTwoFaceWindowLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.PositiveRealWindowLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalDebtScalarSplit

/-!
# Diagonal owner limit source

This file owns convergence of the real diagonal-debt windows to the owner
completed diagonal-debt real part.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The finite completed two-face/GNS matrix-window real scalar is the
diagonal-debt real window minus the positive real window. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_eq_diagonalDebt_sub_positiveWindow_re_source
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) =
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
        zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveWindow N f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f
  let hexpansion : P + T = D :=
    zetaCompletedPrimeDefectKernelPositiveWindow_add_twoFaceWindow_eq_diagonalDebtWindow
      N f
  let hrealAdd :
      Complex.re P + Complex.re T = Complex.re (P + T) :=
    (Complex.add_re P T).symm
  let hrealTarget :
      Complex.re (P + T) = Complex.re D :=
    congrArg Complex.re hexpansion
  let hreal :
      Complex.re P + Complex.re T = Complex.re D :=
    hrealAdd.trans hrealTarget
  let hrealSwapped :
      Complex.re T + Complex.re P = Complex.re D :=
    (add_comm (Complex.re T) (Complex.re P)).trans hreal
  let hsolve :
      Complex.re T = Complex.re D - Complex.re P :=
    eq_sub_of_add_eq hrealSwapped
  let hstart :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) =
        Complex.re T :=
    Eq.refl (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
  let hfinish :
      Complex.re D - Complex.re P =
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
          zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
    Eq.refl
      (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
        zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
  hstart.trans (hsolve.trans hfinish)

/-- The diagonal-debt real window is the sum of the two-face real window and
the positive real window. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_twoFace_re_add_positiveRealWindow_source_core
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
        zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
  let hsub :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) =
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
          zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_eq_diagonalDebt_sub_positiveWindow_re_source
      N f
  let hadd :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
          zetaCompletedPrimeDefectKernelPositiveRealWindow N f =
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f :=
    (sub_eq_iff_eq_add.mp hsub.symm).symm
  hadd.symm

/-- The diagonal-debt real-window stream is the sum of the two-face real stream
and the positive real-window stream. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_stream_eq_twoFace_re_add_positiveRealWindow_source
    (f : ZetaAdmissibleFunction) :
    (fun N : ℕ =>
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f) =
      fun N : ℕ =>
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
          zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
  funext
    (fun N : ℕ =>
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_twoFace_re_add_positiveRealWindow_source_core
        N f)

/-- Source convergence of real diagonal-debt windows to the owner completed
diagonal-debt real part. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_source_primitive
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
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
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_ownerMatrixCoefficient_re_source_primitive
      f hmajorant
  let hpositive :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_ownerPositiveChannel_source_primitive
      f hmajorant hcoordinateZero
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

/-- Source convergence of real diagonal-debt windows to the owner completed
diagonal-debt real part, with positive/off-diagonal gap vanishing explicitly
supplied. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_of_positiveOffDiagonalGap_eq_zero_source_primitive
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
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
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_ownerMatrixCoefficient_re_source_primitive
      f hmajorant
  let hpositive :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_ownerPositiveChannel_of_positiveOffDiagonalGap_eq_zero_source_primitive
      f D hmajorant hgapZero
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
