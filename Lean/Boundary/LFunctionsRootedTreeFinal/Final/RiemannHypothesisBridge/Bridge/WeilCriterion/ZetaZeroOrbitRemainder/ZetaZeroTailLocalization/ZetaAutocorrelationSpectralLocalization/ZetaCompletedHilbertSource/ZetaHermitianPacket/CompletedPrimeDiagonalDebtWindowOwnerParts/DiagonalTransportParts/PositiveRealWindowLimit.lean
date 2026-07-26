import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.SpectralMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.OwnerParts.Part04

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

theorem complex_tendsto_sum_window_of_hasSum_positiveRealWindowLimit
    (a : ZetaPrimePowerIndex → ℂ) (x : ℂ)
    (hsum : HasSum a x)
    (hzero :
      ∀ index : ZetaPrimePowerIndex,
        ¬ ZetaPrimePowerIndex.IsGenuine index → a index = 0) :
    Tendsto
      (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.window N, a index)
      atTop
      (𝓝 x) :=
  let hbox :
      Tendsto
        (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.box N, a index)
        atTop
        (𝓝 x) :=
    ZetaPrimePowerIndex.tendsto_sum_box_of_hasSum_complex
      a x hsum
  let hbox_eq_window :
      (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.box N, a index) =
      (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.window N, a index) :=
    funext
      (fun N : ℕ =>
        ZetaPrimePowerIndex.sum_box_eq_sum_window_of_zero_not_isGenuine
          a hzero N)
  Eq.subst
    (motive := fun stream : ℕ → ℂ => Tendsto stream atTop (𝓝 x))
    hbox_eq_window
    hbox

theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_eq_zero_of_not_isGenuine_positiveRealWindowLimit
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hindex : ¬ ZetaPrimePowerIndex.IsGenuine index) :
    zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f = 0 :=
  let hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinate index f = 0 :=
    zetaCompletedPrimeDefectKernelPositiveCoordinate_eq_zero_of_not_isGenuine
      index f hindex
  let hdiagonalCoordinate :
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f = 0 :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_eq_zero_of_not_isGenuine
      index f hindex
  let hdecomposition :
      zetaCompletedPrimeDefectKernelPositiveCoordinate index f +
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f =
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
      index f
  let hstart :
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f =
        0 + zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f :=
    (zero_add
      (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)).symm
  let hpositive :
      0 + zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f =
        zetaCompletedPrimeDefectKernelPositiveCoordinate index f +
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f :=
    congrArg
      (fun value : ℂ =>
        value + zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
      hpositiveCoordinate.symm
  hstart.trans (hpositive.trans (hdecomposition.trans hdiagonalCoordinate))

theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_hasSum_matrixCoefficient_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hsummable :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) :=
    summable_zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_of_spectralMajorant
      f
      hmajorant
  let hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
        (∑' index : ZetaPrimePowerIndex,
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) :=
    hsummable.hasSum
  let htarget :
      (∑' index : ZetaPrimePowerIndex,
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f :=
    zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_tsum_eq_matrixCoefficient
      f
  Eq.subst
    (motive := fun value : ℂ =>
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
        value)
    htarget
    hhasSum

theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_windowSum_eq_matrixCoefficientWindow_positiveRealWindowLimit
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.window N,
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
  let orientedSeries : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSOrientedCoordinate index f
  let hsum :
      (∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
      (∑ index in ZetaPrimePowerIndex.window N,
        orientedSeries index) +
        (∑ index in ZetaPrimePowerIndex.window N,
          star (orientedSeries index)) :=
    Finset.sum_add_distrib
  let hstar :
      (∑ index in ZetaPrimePowerIndex.window N,
        star (orientedSeries index)) =
      star
        (∑ index in ZetaPrimePowerIndex.window N,
          orientedSeries index) :=
    (star_sum
      (ZetaPrimePowerIndex.window N)
      orientedSeries).symm
  let hstarTransport :
      (∑ index in ZetaPrimePowerIndex.window N,
        orientedSeries index) +
          (∑ index in ZetaPrimePowerIndex.window N,
            star (orientedSeries index)) =
        (∑ index in ZetaPrimePowerIndex.window N,
          orientedSeries index) +
          star
            (∑ index in ZetaPrimePowerIndex.window N,
              orientedSeries index) :=
    congrArg
      (fun value : ℂ =>
        (∑ index in ZetaPrimePowerIndex.window N,
          orientedSeries index) + value)
      hstar
  let hdefinition :
      (∑ index in ZetaPrimePowerIndex.window N,
        orientedSeries index) +
        star
          (∑ index in ZetaPrimePowerIndex.window N,
            orientedSeries index) =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
    Eq.refl (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)
  hsum.trans (hstarTransport.trans hdefinition)

theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_windowSum_sequence_eq_matrixCoefficientWindow_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction) :
    (fun N : ℕ =>
      ∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
      (fun N : ℕ => zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) :=
  funext
    (fun N : ℕ =>
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_windowSum_eq_matrixCoefficientWindow_positiveRealWindowLimit
        N f)

theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_matrixCoefficient_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)) :=
  let twoFaceSeries : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f
  let hseries :
      twoFaceSeries =
        fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f :=
    Eq.refl twoFaceSeries
  let hhasSum :
      HasSum twoFaceSeries
        (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    Eq.subst
      (motive := fun stream : ZetaPrimePowerIndex → ℂ =>
        HasSum stream
          (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
      hseries.symm
      (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_hasSum_matrixCoefficient_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
        f hmajorant)
  let hzero :
      ∀ index : ZetaPrimePowerIndex,
        ¬ ZetaPrimePowerIndex.IsGenuine index →
          twoFaceSeries index = 0 :=
    fun index : ZetaPrimePowerIndex =>
      fun hindex : ¬ ZetaPrimePowerIndex.IsGenuine index =>
        Eq.subst
          (motive := fun value : ℂ => value = 0)
          (congrFun hseries index).symm
          (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_eq_zero_of_not_isGenuine_positiveRealWindowLimit
            index f hindex)
  let hlimit :
      Tendsto
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.window N, twoFaceSeries index)
        atTop
        (𝓝 (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)) :=
    complex_tendsto_sum_window_of_hasSum_positiveRealWindowLimit
      twoFaceSeries
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
      hhasSum
      hzero
  let hseriesWindow :
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.window N, twoFaceSeries index) =
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) :=
    funext
      (fun N : ℕ =>
        Finset.sum_congr
          (Eq.refl (ZetaPrimePowerIndex.window N))
          (fun index membership =>
            congrFun hseries index))
  let hwindow :
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.window N, twoFaceSeries index) =
      (fun N : ℕ => zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) :=
    hseriesWindow.trans
      (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_windowSum_sequence_eq_matrixCoefficientWindow_positiveRealWindowLimit
        f)
  Eq.subst
    (motive := fun stream : ℕ → ℂ =>
      Tendsto stream atTop
        (𝓝 (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)))
    hwindow
    hlimit

theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_input_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  hcoordinateZero

theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hledger :
      ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f :=
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_owner f
  let horiented :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f) :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_owner
      f
  completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_boundaryCancellation
    f hledger horiented

/-- Majorant summability gives vanishing of the real owner completed
diagonal-debt scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 :=
  zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_twoFace_re_eq
    f
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
      f hmajorant)

/-- Majorant summability identifies the raw completed diagonal-debt coordinate
presentation with the real owner completed diagonal-debt scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerRe_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_of_input_positiveRealWindowLimit
    f hcoordinateZero).trans
    (zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
      f hmajorant).symm

/-- Majorant summability gives convergence of completed diagonal-debt real
windows to the real owner completed diagonal debt. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerRe_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
  let hcoordinate :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝
          (Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
      f
      hmajorant
  let htarget :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerRe_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
      f hmajorant hcoordinateZero
  Eq.subst
    (motive := fun value : ℝ =>
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 value))
    htarget
    hcoordinate

/-- The completed diagonal-debt real windows converge to the real owner
completed diagonal debt. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerRe_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
  zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerRe_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f
    hmajorant
    hcoordinateZero

/-- Majorant summability gives convergence of the completed two-face
matrix-window real scalars to the real owner completed two-face matrix
coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_matrixCoefficient_re_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ =>
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))) :=
  let hcomplex :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)) :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_matrixCoefficient_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
      f hmajorant
  let hreMap :
      Tendsto Complex.re
        (𝓝 (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
        (𝓝 (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))) :=
    Complex.continuous_re.tendsto
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
  hreMap.comp hcomplex

/-- The completed positive windows are diagonal-debt windows minus two-face
matrix-coefficient windows. -/
theorem zetaCompletedPrimeDefectKernelPositiveWindow_eq_diagonalDebtWindow_sub_twoFaceWindow_positiveRealWindowLimit
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveWindow N f =
      zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f -
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
  let hexpansion :
      zetaCompletedPrimeDefectKernelPositiveWindow N f +
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f =
        zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f :=
    zetaCompletedPrimeDefectKernelPositiveWindow_add_twoFaceWindow_eq_diagonalDebtWindow
      N f
  let hstart :
      zetaCompletedPrimeDefectKernelPositiveWindow N f =
        (zetaCompletedPrimeDefectKernelPositiveWindow N f +
            zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) -
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
    (add_sub_cancel_right
      (zetaCompletedPrimeDefectKernelPositiveWindow N f)
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)).symm
  let htransport :
      (zetaCompletedPrimeDefectKernelPositiveWindow N f +
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) -
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f =
        zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f -
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
    congrArg
      (fun value : ℂ =>
        value - zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)
      hexpansion
  hstart.trans htransport

/-- Real parts turn the complex positive-window subtraction identity into the
real-window subtraction identity. -/
theorem zetaCompletedPrimeDefectKernelPositiveWindow_sub_re_eq_diagonalDebtReal_sub_twoFace_re_positiveRealWindowLimit
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f -
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) =
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) :=
  Complex.sub_re
    (zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f)
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)

/-- The completed positive real window is the diagonal-debt real window minus
the real two-face matrix-coefficient window. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_eq_diagonalDebtRealWindow_sub_twoFaceWindow_re_positiveRealWindowLimit
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveRealWindow N f =
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) :=
  let hcomplex :
      zetaCompletedPrimeDefectKernelPositiveWindow N f =
        zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f -
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
    zetaCompletedPrimeDefectKernelPositiveWindow_eq_diagonalDebtWindow_sub_twoFaceWindow_positiveRealWindowLimit
      N f
  let hre :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f -
            zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) =
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) :=
    zetaCompletedPrimeDefectKernelPositiveWindow_sub_re_eq_diagonalDebtReal_sub_twoFace_re_positiveRealWindowLimit
      N f
  let hpositiveReal :
      zetaCompletedPrimeDefectKernelPositiveRealWindow N f =
        Complex.re (zetaCompletedPrimeDefectKernelPositiveWindow N f) :=
    Eq.refl (zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
  let hcomplexRe :
      Complex.re (zetaCompletedPrimeDefectKernelPositiveWindow N f) =
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f -
            zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) :=
    congrArg Complex.re hcomplex
  hpositiveReal.trans (hcomplexRe.trans hre)

/-- The owner positive channel is the real part of the owner positive form. -/
theorem completedPrimeDefectKernelPositiveChannel_eq_positiveForm_re_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction) :
    completedPrimeDefectKernelPositiveChannel f =
      Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) :=
  Eq.refl (completedPrimeDefectKernelPositiveChannel f)

/-- Majorant summability gives convergence of completed positive real windows
to the raw coordinate-presentation scalar. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsumRe_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
  zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
    f
    hmajorant

/-- The completed positive real windows converge to the raw coordinate
presentation scalar. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsumRe_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
  zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsumRe_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f
    hmajorant

/-- The real target from diagonal debt minus two-face equals the owner positive
channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveChannel_eq_diagonalDebt_re_sub_twoFace_re_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) -
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      completedPrimeDefectKernelPositiveChannel f :=
  let hsub :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) -
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebt f -
            zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    (Complex.sub_re
      (zetaCompletedPrimeDefectKernelDiagonalDebt f)
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)).symm
  let hdefinition :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebt f -
            zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        completedPrimeDefectKernelPositiveChannel f :=
    Eq.refl (completedPrimeDefectKernelPositiveChannel f)
  hsub.trans hdefinition

/-- Majorant summability gives convergence of completed positive real windows
to the owner positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
  let hdiagonal :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerRe_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
      f hmajorant hcoordinateZero
  let htwoFace :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))) :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_matrixCoefficient_re_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
      f hmajorant
  let hsub :
      Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
            Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
        atTop
        (𝓝
          (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) -
            Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))) :=
    hdiagonal.sub htwoFace
  let hwindow :
      (fun N : ℕ =>
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)) =
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f) :=
    funext
      (fun N : ℕ =>
        (zetaCompletedPrimeDefectKernelPositiveRealWindow_eq_diagonalDebtRealWindow_sub_twoFaceWindow_re_positiveRealWindowLimit
          N f).symm)
  let htarget :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) -
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveChannel_eq_diagonalDebt_re_sub_twoFace_re_positiveRealWindowLimit
      f
  Eq.subst
    (motive := fun value : ℝ =>
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 value))
    htarget
    (Eq.subst
      (motive := fun stream : ℕ → ℝ =>
        Tendsto stream atTop
          (𝓝
            (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) -
              Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))))
      hwindow
      hsub)

/-- The completed positive real windows converge to the owner positive
channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
  zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f
    hmajorant
    hcoordinateZero

/-- Majorant summability identifies the raw completed positive coordinate real
scalar with the owner positive channel by uniqueness of the positive
real-window limit. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  let hcoordinate :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsumRe_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
      f hmajorant
  let howner :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
      f hmajorant hcoordinateZero
  tendsto_nhds_unique hcoordinate howner

/-- The raw completed positive coordinate real scalar equals the owner
positive channel by uniqueness of the positive real-window limit. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_positiveRealWindowLimit
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f
    hmajorant
    hcoordinateZero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
