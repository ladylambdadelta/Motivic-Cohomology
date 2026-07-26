import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ResidualCoordinate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.PositiveRealWindowLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeSpectralMajorantSummability

/-!
# Completed two-face window limit source

This file owns convergence of the completed two-face matrix windows to the
owner completed two-face GNS matrix coefficient.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped BigOperators Topology

namespace ZetaAdmissibleFunction

/-- Nongenuine prime-power indices have zero completed two-face/GNS
symmetrized coordinate. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_eq_zero_of_not_isGenuine_windowLimit_source
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hindex : ¬ ZetaPrimePowerIndex.IsGenuine index) :
    zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f = 0 :=
  let C : ℂ := zetaCompletedPrimeTwoFaceGNSOrientedCoordinate index f
  let hweight : ZetaPrimePowerIndex.weight index = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine index hindex
  let hC_weighted :
      C =
        (index.weight : ℂ) *
          (zetaCompletedExplicitFormulaPhi f index.center *
            star
              (zetaCompletedExplicitFormulaPhi
                f (-(index.center : ℂ)))) :=
    zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_eq_weightedSeedPair
      index f
  let hC_zeroWeight :
      (index.weight : ℂ) *
          (zetaCompletedExplicitFormulaPhi f index.center *
            star
              (zetaCompletedExplicitFormulaPhi
                f (-(index.center : ℂ)))) =
        (0 : ℂ) *
          (zetaCompletedExplicitFormulaPhi f index.center *
            star
              (zetaCompletedExplicitFormulaPhi
                f (-(index.center : ℂ)))) :=
    congrArg
      (fun value : ℝ =>
        (value : ℂ) *
          (zetaCompletedExplicitFormulaPhi f index.center *
            star
              (zetaCompletedExplicitFormulaPhi
                f (-(index.center : ℂ)))))
      hweight
  let hC_zero :
      (0 : ℂ) *
          (zetaCompletedExplicitFormulaPhi f index.center *
            star
              (zetaCompletedExplicitFormulaPhi
                f (-(index.center : ℂ)))) =
        0 :=
    zero_mul
      (zetaCompletedExplicitFormulaPhi f index.center *
        star
          (zetaCompletedExplicitFormulaPhi
            f (-(index.center : ℂ))))
  let hC : C = 0 :=
    Eq.trans hC_weighted (Eq.trans hC_zeroWeight hC_zero)
  let hsymm :
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f =
        C + star C :=
    Eq.refl (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
  let hCadd : C + star C = 0 + star 0 :=
    congrArg₂ HAdd.hAdd hC (congrArg star hC)
  let hstarZero : 0 + star (0 : ℂ) = 0 + 0 :=
    congrArg (fun value : ℂ => 0 + value) (star_zero ℂ)
  let haddZero : (0 : ℂ) + 0 = 0 :=
    zero_add 0
  Eq.trans hsymm
    (Eq.trans hCadd
      (Eq.trans hstarZero haddZero))

/-- The finite sum of completed symmetrized two-face/GNS coordinates is the
completed two-face/GNS matrix window. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_sum_eq_matrixWindow_windowLimit_source
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
  let s : Finset ZetaPrimePowerIndex := ZetaPrimePowerIndex.window N
  let C : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSOrientedCoordinate index f
  let hwindow :
      (∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
        (∑ index in s,
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) :=
    Eq.refl
      (∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
  let hcoordinate :
      Finset.sum s
          (fun ι : ZetaPrimePowerIndex =>
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
        Finset.sum s (fun ι : ZetaPrimePowerIndex => (C ι) + star (C ι)) :=
    Finset.sum_congr
      (Eq.refl s)
      (fun ι _hmembership =>
        Eq.refl
          (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f))
  let hsum :
      Finset.sum s (fun ι : ZetaPrimePowerIndex => (C ι) + star (C ι)) =
        Finset.sum s C +
          Finset.sum s (fun ι : ZetaPrimePowerIndex => star (C ι)) :=
    Finset.sum_add_distrib
  let hstar :
      (∑ index in s,
          star (C index)) =
        star (∑ index in s, C index) :=
    (star_sum s C).symm
  let hstarAdd :
      (∑ index in s, C index) + (∑ index in s, star (C index)) =
        (∑ index in s, C index) + star (∑ index in s, C index) :=
    congrArg
      (fun value : ℂ => (∑ index in s, C index) + value)
      hstar
  let hmatrix :
      (∑ index in s, C index) + star (∑ index in s, C index) =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
    Eq.refl (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)
  Eq.trans hwindow
    (Eq.trans hcoordinate
      (Eq.trans hsum
        (Eq.trans hstarAdd hmatrix)))

/-- Completed two-face/GNS matrix windows exhaust the owner completed
two-face/GNS matrix coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_ownerMatrixCoefficient_windowLimit_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)) :=
  zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_matrixCoefficient_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f hmajorant

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs make completed
two-face/GNS matrix windows exhaust the owner completed two-face/GNS matrix
coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_ownerMatrixCoefficient_of_diagonalDebtCoordinate_re_hasSum_windowLimit_source
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
      (fun N : ℕ => zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_ownerMatrixCoefficient_windowLimit_source
    f hmajorant

/-- Source convergence of completed two-face matrix real windows. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_ownerMatrixCoefficient_re_source_primitive
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
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_ownerMatrixCoefficient_windowLimit_source
      f hmajorant)

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give convergence of
completed two-face matrix real windows. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_ownerMatrixCoefficient_re_of_diagonalDebtCoordinate_re_hasSum_source_primitive
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
      (fun N : ℕ =>
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))) :=
  (Complex.continuous_re.tendsto
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)).comp
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_ownerMatrixCoefficient_of_diagonalDebtCoordinate_re_hasSum_windowLimit_source
      f C Creflect hhasSum hhasSumReflect)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
