import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.CompletedTwoFaceWindowLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalDebtAnnihilatorGapAssembly

/-!
# Completed prime diagonal owner-window limit

This file owns the diagonal part of completed prime trace transport: the
finite diagonal-debt real windows converge to the owner diagonal-debt scalar
once the positive and two-face trace windows have their owner limits.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped BigOperators Topology

namespace ZetaAdmissibleFunction

/-- Nongenuine prime-power indices have zero completed two-face/GNS
symmetrized coordinate. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_eq_zero_of_not_isGenuine_traceTransport_source
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hindex : ¬ ZetaPrimePowerIndex.IsGenuine index) :
    zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f = 0 :=
  zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_eq_zero_of_not_isGenuine_windowLimit_source
    index f hindex

/-- The finite sum of completed symmetrized two-face/GNS coordinates is the
completed two-face/GNS matrix window, at the diagonal-owner source level. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_sum_eq_matrixWindow_traceTransport_source_limit_core
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
  zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_sum_eq_matrixWindow_windowLimit_source
    N f

/-- Completed two-face/GNS matrix windows exhaust the owner completed
two-face/GNS matrix coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_ownerMatrixCoefficient_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)) :=
  zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_ownerMatrixCoefficient_windowLimit_source
    f hmajorant

/-- The finite completed two-face/GNS matrix-window real scalar is the
diagonal-debt real window minus the positive real window, at the
trace-transport source level. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_eq_diagonalDebt_sub_positiveWindow_re_traceTransport_source
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

/-- Source transport of the completed two-face real coefficient to the raw
lower-weight two-face real coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hcompleted :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f
  let hraw :
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
      f
  hcompleted.trans hraw.symm

/-- Source transport of the completed two-face real coefficient to the raw
lower-weight two-face real coefficient, with the positive/off-diagonal gap
vanishing explicitly supplied. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_of_positiveOffDiagonalGap_eq_zero_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hgapZero : completedPrimePositiveOffDiagonalGap f = 0) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hcompleted :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f
  let hraw :
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
      f
  hcompleted.trans hraw.symm

/-- Source lower-weight annihilation of the completed two-face/GNS real
coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
  let htransport :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_source_limit_core
      f hmajorant hcoordinateZero
  let hraw :
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
      f
  htransport.trans hraw

/-- Source lower-weight annihilation of the completed two-face/GNS
matrix-window real scalars. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_zero_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ =>
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
      atTop
      (𝓝 0) :=
  let howner :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))) :=
    (Complex.continuous_re.tendsto
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)).comp
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_ownerMatrixCoefficient_source
        f hmajorant)
  let hzero :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source_limit_core
      f
      hmajorant
      hcoordinateZero
  Eq.subst
    (motive := fun value : ℝ =>
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
        atTop
        (𝓝 value))
    hzero
    howner

/-- Source holographic trace separation annihilates the completed positive
prime-defect coordinate trace directly.  This is the non-diagonal
reconstruction input: the coordinate presentation is killed by the same
completed lower-weight trace character that kills the owner positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  let htransport :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_traceFaithfulness_source
      f hmajorant hcoordinateZero
  let howner :
      completedPrimeDefectKernelPositiveChannel f = 0 :=
    completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
      f
  htransport.trans howner

/-- Source lower-weight annihilation of the completed positive prime-defect
real windows. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_zero_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 0) :=
  let hcoordinate :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
      f
      hmajorant
  let hzero :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_source_limit_core
      f hmajorant hcoordinateZero
  Eq.subst
    (motive := fun value : ℝ =>
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 value))
    hzero
    hcoordinate

/-- The completed diagonal-debt real window is the completed two-face real
window plus the completed positive real window. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_twoFace_re_add_positiveRealWindow_source_core
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
        zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
  let hsub :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) =
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
          zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_eq_diagonalDebt_sub_positiveWindow_re_traceTransport_source
      N f
  let hadd :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
          zetaCompletedPrimeDefectKernelPositiveRealWindow N f =
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f :=
    (sub_eq_iff_eq_add.mp hsub.symm).symm
  hadd.symm

/-- Source lower-weight annihilation of the finite completed diagonal-debt
real windows. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_zero_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 0) :=
  let htwoFace :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
        atTop
        (𝓝 0) :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_zero_source_limit_core
      f hmajorant hcoordinateZero
  let hpositive :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 0) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_zero_source_limit_core
      f hcoordinateZero hmajorant
  let hadd :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (0 + 0)) :=
    htwoFace.add hpositive
  let hzero : (0 : ℝ) + 0 = 0 :=
    zero_add 0
  let haddZero :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun value : ℝ =>
        Tendsto
          (fun N : ℕ =>
            Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
              zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
          atTop
          (𝓝 value))
      hzero
      hadd
  let hfun :
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f) =
        fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
    funext
      (fun N : ℕ =>
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_twoFace_re_add_positiveRealWindow_source_core
        N f)
  Eq.subst
    (motive := fun stream : ℕ → ℝ =>
      Tendsto stream atTop (𝓝 0))
    hfun.symm
    haddZero

/-- Source lower-weight annihilation of the raw completed diagonal-debt
coordinate presentation. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  hcoordinateZero

/-- Source lower-weight annihilation of the owner completed diagonal-debt
scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 :=
  zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_twoFace_re_eq
    f
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_source_limit_core
      f hmajorant hcoordinateZero)

/-- Source transport from the raw diagonal-debt coordinate presentation to the
owner completed diagonal-debt scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_source_limit_core
    f hmajorant hcoordinateZero).trans
    (zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_source_limit_core
      f hmajorant hcoordinateZero).symm

/-- Source reconstruction of the raw positive coordinate total as the owner
completed positive prime-defect channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
    f
    hmajorant
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_source_limit_core
      f hmajorant hcoordinateZero)

/-- Source owner limit of the completed positive prime-defect real windows. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_ownerPositiveChannel_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
  zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_of_coordinateTsum_re
    f
    hmajorant
    (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_source_limit_core
      f hmajorant hcoordinateZero)

/-- Source owner limit of the completed two-face/GNS matrix-window real
scalars. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_ownerMatrixCoefficient_re_source_limit_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ =>
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))) :=
  (Complex.continuous_re.tendsto
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)).comp
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_ownerMatrixCoefficient_source
      f hmajorant)

/-- The owner completed diagonal debt real scalar is the owner positive
channel plus the completed two-face/GNS real scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_positiveChannel_add_twoFace_re_source_core
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedPrimeDefectKernelPositiveChannel f +
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let hpositive :
      completedPrimeDefectKernelPositiveChannel f = Complex.re P :=
    Eq.refl (completedPrimeDefectKernelPositiveChannel f)
  let hexpansion :
      P + T = D :=
    zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms
      f
  let hstart :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        Complex.re D :=
    Eq.refl (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
  let hexpansionRe :
      Complex.re D = Complex.re (P + T) :=
    congrArg Complex.re hexpansion.symm
  let haddRe :
      Complex.re (P + T) = Complex.re P + Complex.re T :=
    Complex.add_re P T
  let hpositiveRe :
      Complex.re P + Complex.re T =
        completedPrimeDefectKernelPositiveChannel f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    congrArg
      (fun value : ℝ =>
        value + Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
      hpositive.symm
  hstart.trans (hexpansionRe.trans (haddRe.trans hpositiveRe))

/-- Source owner limit of the completed diagonal-debt real windows. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_source_limit_core
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
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_ownerMatrixCoefficient_re_source_limit_core
      f hmajorant
  let hpositive :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_ownerPositiveChannel_source_limit_core
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
      (zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_positiveChannel_add_twoFace_re_source_core
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
  let hfun :
      (fun N : ℕ =>
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f) =
        fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
    funext
      (fun N : ℕ =>
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_twoFace_re_add_positiveRealWindow_source_core
        N f)
  Eq.subst
    (motive := fun stream : ℕ → ℝ =>
      Tendsto stream atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))))
    hfun.symm
    haddOwner

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
